// Copyright 2014 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// callgraph: a tool for reporting the call graph of a Go program.
// See Usage for details, or run with -help.
package main

import (
	"bufio"
	"flag"
	"fmt"
	"go/build"
	"go/token"
	"io"
	"log"
	"os"
	"runtime"
	"sort"
	"strings"

	"golang.org/x/tools/go/buildutil"
	"golang.org/x/tools/go/callgraph"
	"golang.org/x/tools/go/callgraph/cha"
	"golang.org/x/tools/go/callgraph/rta"
	"golang.org/x/tools/go/callgraph/static"
	"golang.org/x/tools/go/loader"
	"golang.org/x/tools/go/pointer"
	"golang.org/x/tools/go/ssa"
	"golang.org/x/tools/go/ssa/ssautil"
)

// flags
var (
	algoFlag = flag.String("algo", "rta",
		`Call graph construction algorithm (static, cha, rta, pta)`)

	testFlag = flag.Bool("test", false,
		"Loads test code (*_test.go) for imported packages")

	formatFlag = flag.String("format",
		"{{.Caller}}\t--{{.Dynamic}}-{{.Line}}:{{.Column}}-->\t{{.Callee}}",
		"A template expression specifying how to format an edge")

	ptalogFlag = flag.String("ptalog", "",
		"Location of the points-to analysis log file, or empty to disable logging.")

	fileFlag  = flag.String("file", "", "File that contains the to be examined function")
	lineFlag  = flag.Int("line", -1, "Line that contains the to be examined function")
	depthFlag = flag.Int("depth", 2, "Depth of the callee tree of the output")
)

func init() {
	flag.Var((*buildutil.TagsFlag)(&build.Default.BuildTags), "tags", buildutil.TagsFlagDoc)
}

const Usage = `callgraph: display the the call graph of a Go program.

Usage:

  callgraph [-algo=static|cha|rta|pta] [-test] [-format=...] <args>...

Flags:

-algo      Specifies the call-graph construction algorithm, one of:

            static      static calls only (unsound)
            cha         Class Hierarchy Analysis
            rta         Rapid Type Analysis
            pta         inclusion-based Points-To Analysis

           The algorithms are ordered by increasing precision in their
           treatment of dynamic calls (and thus also computational cost).
           RTA and PTA require a whole program (main or test), and
           include only functions reachable from main.

-test      Include the package's tests in the analysis.
` + loader.FromArgsUsage + `

Examples:

  Show the call graph of the trivial web server application:

    callgraph -format digraph $GOROOT/src/net/http/triv.go

  Same, but show only the packages of each function:

    callgraph -format '{{.Caller.Pkg.Object.Path}} -> {{.Callee.Pkg.Object.Path}}' \
      $GOROOT/src/net/http/triv.go | sort | uniq

  Show functions that make dynamic calls into the 'fmt' test package,
  using the pointer analysis algorithm:

    callgraph -format='{{.Caller}} -{{.Dynamic}}-> {{.Callee}}' -test -algo=pta fmt |
      sed -ne 's/-dynamic-/--/p' |
      sed -ne 's/-->.*fmt_test.*$//p' | sort | uniq

  Show all functions directly called by the callgraph tool's main function:

    callgraph -format=digraph golang.org/x/tools/cmd/callgraph |
      digraph succs golang.org/x/tools/cmd/callgraph.main
`

func init() {
	// If $GOMAXPROCS isn't set, use the full capacity of the machine.
	// For small machines, use at least 4 threads.
	if os.Getenv("GOMAXPROCS") == "" {
		n := runtime.NumCPU()
		if n < 4 {
			n = 4
		}
		runtime.GOMAXPROCS(n)
	}
}

func main() {
	flag.Parse()
	if err := doCallgraph(&build.Default, *algoFlag, *formatFlag, *testFlag, flag.Args()); err != nil {
		fmt.Fprintf(os.Stderr, "callgraph: %s\n", err)
		os.Exit(1)
	}
}

var stdout io.Writer = os.Stdout

func doCallgraph(ctxt *build.Context, algo, format string, tests bool, args []string) error {
	conf := loader.Config{Build: ctxt}

	if len(args) == 0 {
		fmt.Fprintln(os.Stderr, Usage)
		return nil
	}

	if *fileFlag == "" || *lineFlag == -1 {
		fmt.Fprintln(os.Stderr, "Need input file and line")
		return nil
	}

	// Use the initial packages from the command line.
	args, err := conf.FromArgs(args, tests)
	if err != nil {
		return err
	}

	// Load, parse and type-check the whole program.
	iprog, err := conf.Load()
	if err != nil {
		return err
	}

	// Create and build SSA-form program representation.
	prog := ssautil.CreateProgram(iprog, 0)
	prog.Build()

	// -- call graph construction ------------------------------------------

	var cg *callgraph.Graph

	switch algo {
	case "static":
		cg = static.CallGraph(prog)

	case "cha":
		cg = cha.CallGraph(prog)

	case "pta":
		// Set up points-to analysis log file.
		var ptalog io.Writer
		if *ptalogFlag != "" {
			if f, err := os.Create(*ptalogFlag); err != nil {
				log.Fatalf("Failed to create PTA log file: %s", err)
			} else {
				buf := bufio.NewWriter(f)
				ptalog = buf
				defer func() {
					if err := buf.Flush(); err != nil {
						log.Printf("flush: %s", err)
					}
					if err := f.Close(); err != nil {
						log.Printf("close: %s", err)
					}
				}()
			}
		}

		main, err := mainPackage(prog, tests)
		if err != nil {
			return err
		}
		config := &pointer.Config{
			Mains:          []*ssa.Package{main},
			BuildCallGraph: true,
			Log:            ptalog,
		}
		ptares, err := pointer.Analyze(config)
		if err != nil {
			return err // internal error in pointer analysis
		}
		cg = ptares.CallGraph

	case "rta":
		main, err := mainPackage(prog, tests)
		if err != nil {
			return err
		}
		roots := []*ssa.Function{
			main.Func("init"),
			main.Func("main"),
		}
		rtares := rta.Analyze(roots, true)
		cg = rtares.CallGraph

		// NB: RTA gives us Reachable and RuntimeTypes too.

	default:
		return fmt.Errorf("unknown algorithm: %s", algo)
	}

	cg.DeleteSyntheticNodes()

	// -- output------------------------------------------------------------

	file := *fileFlag
	line := *lineFlag
	depth := *depthFlag

	node := findFunction(cg, file, line)
	if node == nil {
		panic("function not found")
	}

	ins, before := ChainBefore(node)
	after, outs := ChainAfter(node)
	fmt.Println(len(ins), len(before), len(after), len(outs))
	chain := append(before, after[1:]...)

	sort.Sort(SortNodes(ins))
	for _, n := range ins {
		_, ch := ChainBefore(n)
		fmt.Printf("(%d) %s\n", impact(ch[0]), chainToString(ch))
	}
	fmt.Println()
	fmt.Println(chainToString(chain))
	fmt.Println()

	sort.Sort(SortNodes(outs))
	for _, n := range outs {
		if impact(n) > minImpact {
			continue
		}
		printFanout(depth, "", n)
	}

	return nil
}

var minImpact = 15

type SortNodes []*callgraph.Node

func (v SortNodes) Len() int           { return len(v) }
func (v SortNodes) Less(i, j int) bool { return impact(v[i]) < impact(v[j]) }
func (v SortNodes) Swap(i, j int)      { v[i], v[j] = v[j], v[i] }

func findFunction(cg *callgraph.Graph, file string, line int) *callgraph.Node {
	// get function
	for f, node := range cg.Nodes {
		if f == nil {
			continue
		}

		p := f.Prog.Fset.Position(f.Pos())
		if p.Filename == file && line == p.Line {
			return node
		}
	}

	return nil
}

func OutNodes(n *callgraph.Node) []*callgraph.Node {
	edges := n.Out
	outsM := make(map[*callgraph.Node]struct{})
	for _, edge := range edges {
		outsM[edge.Callee] = struct{}{}
	}
	var outs []*callgraph.Node
	for k := range outsM {
		outs = append(outs, k)
	}
	return outs
}

func InNodes(n *callgraph.Node) []*callgraph.Node {
	edges := n.In
	insM := make(map[*callgraph.Node]struct{})
	for _, edge := range edges {
		insM[edge.Caller] = struct{}{}
	}
	var ins []*callgraph.Node
	for k := range insM {
		ins = append(ins, k)
	}
	return ins
}

func ChainBefore(n *callgraph.Node) (ins, before []*callgraph.Node) {
	before = append(before, n)
	for len(InNodes(n)) == 1 {
		n = n.In[0].Caller
		before = append(before, n)
	}
	// reverse array
	for i := 0; i < len(before)/2; i++ {
		before[i], before[len(before)-1-i] = before[len(before)-1-i], before[i]
	}
	return InNodes(n), before
}

func ChainAfter(n *callgraph.Node) (chain, outs []*callgraph.Node) {
	chain = append(chain, n)
	for len(OutNodes(n)) == 1 {
		n = n.Out[0].Callee
		chain = append(chain, n)
	}
	return chain, OutNodes(n)
}

func printFanout(d int, pfx string, callee *callgraph.Node) {
	if d == -1 {
		return
	}

	ch, after := ChainAfter(callee)
	fmt.Printf("%s(%d) %s\n", pfx, impact(ch[0]), chainToString(ch))

	sort.Sort(SortNodes(after))
	for _, n := range after {
		if impact(n) > minImpact {
			continue
		}
		printFanout(d-1, pfx+"  ", n)
	}
}

// lower is more impact
func impact(n *callgraph.Node) int {
	return len(InNodes(n))
}

func chainToString(chain []*callgraph.Node) string {
	if len(chain) == 0 {
		return ""
	}

	r := chain[0].Func.RelString(chain[0].Func.Pkg.Pkg)
	if strings.Contains(r, "$") {
		r = ""
	}
	for i := 1; i < len(chain); i++ {

		str := chain[i].Func.RelString(chain[i].Func.Pkg.Pkg)
		if strings.Contains(str, "$") {
			continue
		}
		r += " → "
		// r += " -> "
		r += str
	}

	return r
}

// func nodeToString(n *callgraph.Node) string {
// 	t := ""
// 	if len(n.Func.Params) > 0 && n.Func.Signature.Recv() != nil {
// 		t = n.Func.Signature.Recv().Type().String()
// 		p := ""
// 		if len(t) > 0 && t[0] == '*' {
// 			p = "*"
// 		}
// 		i := strings.LastIndex(t, ".")
// 		t = p + t[i+1:] + "."
// 		// t = n.Func.Params[0].Type().String() + "."
// 	} else {
// 		t = n.Func.Pkg.String() + "."
// 		t = t[len("package "):]
// 		i := strings.LastIndex(t, "/")
// 		t = t[i+1:]
// 	}

// 	return t + n.Func.Name()
// }

// mainPackage returns the main package to analyze.
// The resulting package has a main() function.
func mainPackage(prog *ssa.Program, tests bool) (*ssa.Package, error) {
	pkgs := prog.AllPackages()

	// TODO(adonovan): allow independent control over tests, mains and libraries.
	// TODO(adonovan): put this logic in a library; we keep reinventing it.

	if tests {
		// If -test, use all packages' tests.
		if len(pkgs) > 0 {
			if main := prog.CreateTestMainPackage(pkgs...); main != nil {
				return main, nil
			}
		}
		return nil, fmt.Errorf("no tests")
	}

	// Otherwise, use the first package named main.
	for _, pkg := range pkgs {
		if pkg.Pkg.Name() == "main" {
			if pkg.Func("main") == nil {
				return nil, fmt.Errorf("no func main() in main package")
			}
			return pkg, nil
		}
	}

	return nil, fmt.Errorf("no main package")
}

type Edge struct {
	Caller *ssa.Function
	Callee *ssa.Function

	edge     *callgraph.Edge
	fset     *token.FileSet
	position token.Position // initialized lazily
}

func (e *Edge) pos() *token.Position {
	if e.position.Offset == -1 {
		e.position = e.fset.Position(e.edge.Pos()) // called lazily
	}
	return &e.position
}

func (e *Edge) Filename() string { return e.pos().Filename }
func (e *Edge) Column() int      { return e.pos().Column }
func (e *Edge) Line() int        { return e.pos().Line }
func (e *Edge) Offset() int      { return e.pos().Offset }

func (e *Edge) Dynamic() string {
	if e.edge.Site != nil && e.edge.Site.Common().StaticCallee() == nil {
		return "dynamic"
	}
	return "static"
}

func (e *Edge) Description() string { return e.edge.Description() }
