// ghoulbert.go - proof verifier for a variant of the Ghilbert proof language
// Copyright (C) 2010 Dan Krejsa

//  This program is free software: you can redistribute it and/or modify
//  it under the terms of the GNU General Public License as published by
//  the Free Software Foundation, either version 3 of the License, or
//  (at your option) any later version.

//  This program is distributed in the hope that it will be useful,
//  but WITHOUT ANY WARRANTY; without even the implied warranty of
//  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//  GNU General Public License for more details.

//  You should have received a copy of the GNU General Public License
//  along with this program.  If not, see <http://www.gnu.org/licenses/>.


// The Ghilbert (g-Hilbert) proof language was invented by Raph Levien,
// as a component of a system for publishing mathematical proofs on the Web.
// It was inspired by the Metamath system. The Ghilbert language is still
// evolving.
//
// Ghoulbert is based on an earlier version of the Ghilbert language. 
// Starting from that version, Ghoulbert adds the following experimental
// changes:
//
//   * Inference rules may have multiple conclusions as well as multiple
//     hypotheses.
//
//   * Definitions containing dummy variables require a well-definedness
//     proof justifying their independence of the choice of dummy variables.
//
//   * The collection of kinds is partially ordered; some kinds can be
//     'subkinds' of other kinds. In particular, 'set' variables need not
//     have an explicit conversion to 'class' variables.
//
//   * At present, there are no facilities for import (or export) of proof
//     interface files.  Rather, axioms (stmt) are allowed in the same file
//     as theorems (thm).  An import mechanism somewhat different from
//     Ghilbert's may be introduced in the future.
//
// Other experimental changes are likely to be introduced in Ghoulbert.
// The aim of this experimentation is to keep the verifier simple and general
// and useful as a base for sound logical theories while increasing the
// convenience and naturalness of proofs.

package main

import (
    "fmt"
    "os"
    "flag"
    "unicode"
    "utf8"
)

const (
    bufsz   = 8192
    prelude = 8
)

func errMsg(format string, args ...interface{}) {
    fmt.Fprintf(os.Stderr, format, args)
}

type Atom string // since we can't add methods to the 'string' type

type Kind struct {
    name *Atom // note, *Atom rather than string since we use interned
    // atoms
    bits []uint32 // implements subkind relationship
}

func (k1 *Kind) isSubkindOf(k2 *Kind) bool {

    l1 := len(k1.bits)
    // we never extend k.bits without need
    if l1 > len(k2.bits) {
        return false
    }
    for i := 0; i < l1; i++ {
        b1 := k1.bits[i]
        if b1&k2.bits[i] != b1 { return false }
    }
    return true
}

func (k1 *Kind) IsEquivalentTo(k2 *Kind) bool {

    l1 := len(k1.bits)
    // we never extend k.bits without need
    if l1 != len(k2.bits) {
        return false
    }
    for i := 0; i < l1; i++ {
        if k1.bits[i] != k2.bits[i] { return false }
    }
    return true
}


// Make k2 a superkind of k1.
func (k2 *Kind) contain(k1 *Kind) {

    l1 := len(k1.bits)
    if len(k2.bits) < l1 {
        newbits := make([]uint32, l1)
        copy(newbits, k2.bits)
        k2.bits = newbits
    }
    for i := 0; i < l1; i++ {
        k2.bits[i] |= k1.bits[i]
    }
}


// Want to think about using interfaces to represent:
// Kinded objects (a.k.a. expressions)
// Terms
// Parsers

type Kinded interface {
    kind_of() *Kind
}

type Named interface {
    name_of() *Atom
}

type Term struct {
    kind     *Kind
    name     *Atom
    argkinds []*Kind
    expr     Expression  // nil if not a definition term
    nDummies int         // 0 if not a defintion term
}

func (t *Term) arg_kinds() []*Kind { return t.argkinds }

func (t *Term) name_of() *Atom { return t.name }

func (t *Term) kind_of() *Kind { return t.kind }

type Symbolic interface {
    Named
    asVar() *Variable
    asStmt() *Statement
}

type Variable struct {
    kind *Kind
    name *Atom
}

type IVar struct {
    kind  *Kind
    index int
}

type Expression interface {
    kind_of() *Kind
    String() string
    Syntax(vars []*Variable) string
    asIVar() *IVar
    asTermExpr() *TermExpr
}

type TermExpr struct {
    term *Term
    args []Expression
}

func (te *TermExpr) kind_of() *Kind { return te.term.kind_of() }

func (te *TermExpr) asTermExpr() *TermExpr { return te }

func (te *TermExpr) asIVar() *IVar { return nil }

func (te *TermExpr) String() string {
    s := "("
    s += string(*te.term.name_of())
    for _, sub := range te.args {
        s += " "
        s += sub.String()
    }
    s += ")"
    return s
}

func (te *TermExpr) Syntax(vars []*Variable) string {
    s := "("
    s += string(*te.term.name_of())
    for _, sub := range te.args {
        s += " "
        s += sub.Syntax(vars)
    }
    s += ")"
    return s
}


type Statement struct {
    name *Atom

    // In order of occurrence in the hypotheses
    // then conclusions
    vars []*Variable

    // Number of variables in the conclusions not
    // appearing in the hypotheses
    wild_vars int

    hyps  []Expression // Hyps & Concs use IVars
    concs []Expression

    // indices of variables occurring in the hypotheses or
    // conclusions that take part in distinct variables conditions
    dv_vars []int

    // implements a bitmap of n*(n-1)/2 bits, where n = len(dv_vars)
    // Both dv_vars and dv_bits are nil if there are no distinct
    // variables conditions
    dv_bits []uint32

    // Is this an equivalence statement?
    isEquiv bool
}

type Theorem struct {
    Statement

    // Like the proof, hypnames is not really of use after the theorem
    // is proved, unless one stores the proof ...
    hypnames []*Atom // used only in theorems, nil otherwise
}


// Proof-in-Progress structure
type Pip struct {
    allowEquiv bool
    equivDone  bool
    gh         *Ghoulbert
    vars       []*Variable  // variables in hypotheses or conclusions
    pf_stack   []Expression // Proven expressions and wild expressions
    wild_exprs int          // # of wild expressions at top of stack
    hypmap     map[*Atom]int
    varmap     map[*Atom]*IVar
    subst      []Expression // used in applying individual assertions

    // dv_vars is used to accumulate DV conditions while proving a theorem.
    // If n is the number of variables occurring in the hypotheses or
    // conclusions of thm, dv_vars is a bitmap large enough to hold
    // n * (n - 1) / 2 bits (one for each unordered pair of thm's variables)
    dv_pairs    []uint32
    thm_name   *Atom
}

func (pip *Pip) Init(vars []*Variable, hypmap map[*Atom]int, varmap map[*Atom] *IVar) {
    pip.allowEquiv = false
    pip.equivDone = false
    pip.vars = vars
    pip.pf_stack = pip.pf_stack[0:0]
    pip.wild_exprs = 0
    // Delete all the mappings in pip.hypmap
    // for x, _ := range(pip.hypmap) {
    //  pip.hypmap[x] = 0, false
    // }
    pip.hypmap = hypmap
    pip.varmap = varmap
}

func (pip *Pip) Push(e Expression) {
    l := len(pip.pf_stack)
    if l == cap(pip.pf_stack) {
        stack := make([]Expression, l+1, 2*l)
        copy(stack, pip.pf_stack)
        pip.pf_stack = stack
    } else {
        pip.pf_stack = pip.pf_stack[0 : l+1]
    }
    pip.pf_stack[l] = e
}

func (pip *Pip) PushWild(e Expression) {
    pip.Push(e)
    pip.wild_exprs++
}

func (pip *Pip) Apply(stmt *Statement) bool {

    if stmt.isEquiv {
        if !pip.allowEquiv {
            errMsg("Equivalence statements are only allowed at the end\n" +
                   "of a definition justification proof.\n")
            return false
        }
        pip.equivDone = true
    }

    if stmt.wild_vars != pip.wild_exprs {
        errMsg("Assertion %s requrires %d wild variables, " +
               "but %d were provided.\n",
               stmt.name, stmt.wild_vars, pip.wild_exprs)
        return false
    }

    nproven := len(pip.pf_stack) - pip.wild_exprs
    if len(stmt.hyps) > nproven {
        errMsg("Assertion %s requires %d hypotheses, but only " +
               "%d expressions are available on the proof stack.\n",
               stmt.name, len(stmt.hyps), nproven)
        return false
    }

    nsvars := len(stmt.vars)

    if nsvars > cap(pip.subst) {
        pip.subst = make([]Expression, nsvars, nsvars + 8)
    } else {
        pip.subst = pip.subst[0:nsvars]
        for j := 0; j < nsvars; j++ {
            pip.subst[j] = nil
        }
    }

    // Check wild variable kinds
    ix := nproven
    for j := nsvars - stmt.wild_vars; j < nsvars; j++ {
        v := stmt.vars[j]
        k1 := v.kind
        k2 := pip.pf_stack[ix].kind_of()
        if !k2.isSubkindOf(k1) {
            errMsg("Assertion %s wild variable %s has kind %s " +
                   "but substituted with expression of kind %s\n",
               stmt.name, v.name, k1.name, k2.name)
            return false
        }
        pip.subst[j] = pip.pf_stack[ix]
        ix++
    }

    ix = nproven - len(stmt.hyps)
    // Match stmt.hyps against proof stack expressions
    for j := 0; j < len(stmt.hyps); j++ {
        if !MatchExpr(pip.pf_stack[ix], stmt.hyps[j], pip.subst) {
            errMsg("Failed to match %s hypothesis %d\n", stmt.name, j)
            return false
        }
        ix++
    }

    // Check for distinct variable conflicts, and record
    // distinct variable constraints
    if stmt.dv_vars != nil && !pip.DvCheck(stmt) {
        return false
    }

    ix = nproven - len(stmt.hyps)
    nconcs := len(stmt.concs)
    pip.pf_stack = pip.pf_stack[0 : ix+nconcs]
    for j := 0; j < nconcs; j++ {
        pip.pf_stack[ix] = SubstExpr(stmt.concs[j], pip.subst)
        ix++
    }

    pip.wild_exprs = 0
    return true
}

func (pip *Pip) Show () {
    l := len(pip.pf_stack)
    n := l - pip.wild_exprs
    vars := pip.gh.scratch_vars
    var jx int
    for jx = 0; jx < n; jx++ {
        e := pip.pf_stack[jx]
        errMsg("P%-2d  %s\n", jx, e.Syntax(vars))
    }
    for jx < l {
        e := pip.pf_stack[jx]
        errMsg("W%-2d  %s\n", jx - n, e.Syntax(vars))
        jx++
    }
}

func (s *Statement) name_of() *Atom { return s.name }

func (s *Statement) asStmt() *Statement { return s }

func (s *Statement) asVar() *Variable { return nil }

func (s *Statement) asThm() *Theorem { return nil }

func (t *Theorem) asThm() *Theorem { return t }

func (v *Variable) kind_of() *Kind { return v.kind }

func (v *Variable) name_of() *Atom { return v.name }

func (v *Variable) asVar() *Variable { return v }

func (v *Variable) asIVar() *IVar { return nil }

func (v *Variable) asStmt() *Statement { return nil }

func (v *Variable) asTermExpr() *TermExpr { return nil }

func (iv *IVar) kind_of() *Kind { return iv.kind }

func (iv *IVar) asIVar() *IVar { return iv }

func (iv *IVar) asTermExpr() *TermExpr { return nil }

// Ugh, we print an IVar with index x as #x
// Probably we should have used a different API than
// String that also passes in a map from variable indices
// to Variables, or something.
func (iv *IVar) String() string { return fmt.Sprintf("#%d", iv.index) }

func (iv *IVar) Syntax(vars []*Variable) string {
    return string(*vars[iv.index].name)
}


// identifier namespaces
// 1. commands -- not really identifiers, they are keywords
// 2. term symbols.  Term symbols occur only as the first element of an
//    s-expression representing a term expression
// 3. variables and statement/theorem names. Both occur top-level in proofs,
//    as do hypothesis names, which don't have global scope. An identifier
//    that occurs as a proof step and which matches a hypothesis name is
//    taken as a hypothesis name, in preference to a statement/theorem name
//    or a variable name that it might also match.

type FileParser struct {
    file       *os.File
    buf        []byte
    start, end int // invariant start <= end
    eof        bool
    line       int // line number
    atombuf    []byte
    intern     map[string]*Atom
}

func NewFileParser(file *os.File, intern map[string]*Atom) *FileParser {
    if file == nil {
        return nil
    }
    return &FileParser{file, make([]byte, prelude+bufsz),
        0, 0, false, 1, make([]byte, 64), intern}
}

func (p *FileParser) GetRune() (rune, size int) {
    var ix = p.start
    var l = p.end
    var n int = l - ix
    var err os.Error

    for n < 4 && !p.eof {
        copy(p.buf[prelude-n:prelude], p.buf[ix:l])
        ix = prelude - n
        n, err = p.file.Read(p.buf[prelude:])
        if n < 0 {
            errMsg("GetRune: Read failed. error='%s'\n", err.String())
            os.Exit(1)
        } else if n == 0 {
            p.eof = true
        }
        l = prelude + n
        n = l - ix
    }
    p.end = l
    p.start = ix

    // At this point, either l - ix >= 4, or we hit the end of file
    if ix >= l {
        // Must have hit eof.
        return utf8.RuneError, 0
    }

    rune, size = utf8.DecodeRune(p.buf[ix:])
    if rune != utf8.RuneError {
        return rune, size
    }

    errMsg("GetRune: Bad utf8 encoding: ")
    for n = 0; n < size; n++ {
        errMsg(" 0x%2x", p.buf[ix+n])
    }
    errMsg(" .\n")
    os.Exit(1)
    // Not reached; 'return' statement avoids a compiler warning.
    return utf8.RuneError, 0
}

const (
    OPEN_P = iota
    CLOSE_P
    ATOM
    EOFILE
)

func (p *FileParser) GetToken() (code int, atom *Atom) {

    atomlen := 0
    var rune, size int

outer_loop:
    for {
        rune, size = p.GetRune()
        if rune == int('(') {
            if atomlen != 0 {
                break
            }
            p.start += size
            return OPEN_P, nil
        }
        if rune == int(')') {
            if atomlen != 0 {
                break
            }
            p.start += size
            return CLOSE_P, nil
        }
        if unicode.IsSpace(rune) {
            if atomlen != 0 {
                break
            }
            p.start += size
            switch rune {
            case int('\r'):
                rune, size = p.GetRune()
                if rune == int('\n') {
                    p.start += size
                }
                fallthrough
            case int('\n'):
                p.line += 1
            }
            continue
        }
        if rune == int('#') {
            if atomlen != 0 {
                break
            }
            p.start += size
            for {
                rune, size = p.GetRune()
                p.start += size
                switch rune {
                case utf8.RuneError:
                    return EOFILE, nil
                // sequences "\r\n", "\n", and "\r"
                // (where in the last case "\r" is not followed
                // by "\n") could all terminate a one-line
                // comment and cause the line number to
                // increment by one. "\n\r" counts as two
                // lines.
                // "\f" (form feed), "\v" (line tabulation),
                // U+2028 (line separator), and U+2029
                // (paragraph separator) do not terminate
                // the one-line comment nor do they increment
                // the line number.
                case int('\r'):
                    rune, size = p.GetRune()
                    if rune == int('\n') {
                        p.start += size
                    }
                    fallthrough
                case int('\n'):
                    p.line += 1
                    continue outer_loop
                }
            }
            continue
        }
        if rune == utf8.RuneError {
            if atomlen != 0 {
                break
            }
            return EOFILE, nil
        }
        // Treat any other character as an atom character.
        if len(p.atombuf)-atomlen < 4 {
            // grow p.atombuf
            newbuf := make([]byte, 2*len(p.atombuf))
            copy(newbuf, p.atombuf[0:atomlen])
            p.atombuf = newbuf
        }
        // Ugh, re-encoding when the original file already had the
        // encoding...  could just copy.
        // size = utf8.EncodeRune(rune, p.atombuf[atomlen:])
        copy(p.atombuf[atomlen:atomlen+size], p.buf[p.start:])
        p.start += size
        atomlen += size
        // continue...
    }
    name := Atom(p.atombuf[0:atomlen])
    a, found := p.intern[string(name)]
    if found {
        return ATOM, a
    }
    p.intern[string(name)] = &name
    return ATOM, &name
}

type SyntaxItem interface {
    asList() *List
    asAtom() *Atom
    asError() SyntaxErr
    String() string
}

const (
    Syntax_OK = iota
    Syntax_EOF
    Syntax_ERR
)

type SyntaxErr int

type Cons struct {
    car SyntaxItem
    cdr *Cons
}

type List struct {
    head   *Cons
    length int
}

func (e SyntaxErr) String() string {
    switch e {
    case Syntax_EOF:
        return "End of File."
    case Syntax_ERR:
        return "Syntax error."
    }
    return "No error."
}

func (p SyntaxErr) asList() *List { return nil }

func (p SyntaxErr) asAtom() *Atom { return nil }

func (p SyntaxErr) asError() SyntaxErr { return p }

func (l *List) String() string {
    s := "("
    space := ""
    for pr := l.head; pr != nil; pr = pr.cdr {
        s += space
        s += pr.car.String()
        space = " "
    }
    s += ")"
    return s
}

func (p *List) asList() *List { return p }

func (p *List) asAtom() *Atom { return nil }

func (p *List) asError() SyntaxErr { return SyntaxErr(Syntax_OK) }

func (a *Atom) String() string { return string(*a) }

func (a *Atom) asList() *List { return nil }

func (a *Atom) asAtom() *Atom { return a }

func (p *Atom) asError() SyntaxErr { return SyntaxErr(Syntax_OK) }


// Maybe call this 'Lexer'?
type Parser interface {
    GetToken() (code int, atom *Atom)
}

func GetItem(p Parser, in_sexpr bool) SyntaxItem {
    code, atom := p.GetToken()
    if atom != nil {
        return atom
    }
    if code == EOFILE {
        return SyntaxErr(Syntax_EOF)
    }
    if code == CLOSE_P {
        if !in_sexpr {
            errMsg("Unexpected ')' in input.\n")
            return SyntaxErr(Syntax_ERR)
        }
        return nil
    }
    // () should be represented as an empty list which is nil,
    // not Cons{nil, nil}
    // code == OPEN_P
    var head *Cons = nil
    var tail **Cons = &head
    n := 0
    for {
        item := GetItem(p, true)
        if item == nil {
            break
        }
        if item.asError() != Syntax_OK {
            return item
        }
        cons := &Cons{item, nil}
        *tail = cons
        tail = &cons.cdr
        n++
    }
    // TODO: think about reusing some previously used List's and Cons's
    // that are released to a free list rather than returned to the general
    // heap, as a performance optimization.
    list := &List{head, n}
    return list
}


type CommandList struct {
    kind     Atom
    subkind  Atom
    variable Atom // "var" is a keyword
    term     Atom
    stmt     Atom
    def      Atom
    thm      Atom
    equiv    Atom
}

type Ghoulbert struct {
    cmds            CommandList
    kinds           map[*Atom]*Kind
    intern          map[string]*Atom
    syms            map[*Atom]Symbolic // variables and thm/stmt names
    terms           map[*Atom]*Term
    scratch_vars    []*Variable
    scratch_bmap    []uint32
    scratch_varsets [][]uint32
    dv_bmaps    [][]uint32
    pip             Pip
    verbose         uint
}

func NewGhoulbert() *Ghoulbert {
    gh := new(Ghoulbert)

    intern := make(map[string]*Atom, 128)
    gh.cmds.kind = Atom("kind")
    gh.cmds.subkind = Atom("subkind")
    gh.cmds.variable = Atom("var")
    gh.cmds.term = Atom("term")
    gh.cmds.stmt = Atom("stmt")
    gh.cmds.thm = Atom("thm")
    gh.cmds.def = Atom("def")
    gh.cmds.equiv = Atom("equiv")
    // Hmm, consider symbol leak: if a name gets interned,
    // and then is no longer needed, how can we know when it may
    // be removed from the intern map? Maintain a reference count
    // for each name?
    intern[string(gh.cmds.kind)] = &gh.cmds.kind
    intern[string(gh.cmds.subkind)] = &gh.cmds.subkind
    intern[string(gh.cmds.variable)] = &gh.cmds.variable
    intern[string(gh.cmds.term)] = &gh.cmds.term
    intern[string(gh.cmds.stmt)] = &gh.cmds.stmt
    intern[string(gh.cmds.thm)] = &gh.cmds.thm
    intern[string(gh.cmds.def)] = &gh.cmds.def
    intern[string(gh.cmds.equiv)] = &gh.cmds.equiv
    gh.intern = intern
    gh.kinds = make(map[*Atom]*Kind, 128)
    gh.syms = make(map[*Atom]Symbolic, 512)
    gh.terms = make(map[*Atom]*Term, 256)
    gh.scratch_vars = make([]*Variable, 0, 128)
    gh.scratch_bmap = make([]uint32, 2)
    gh.scratch_varsets = make([][]uint32, 16)
    gh.pip.gh = gh
    gh.pip.pf_stack = make([]Expression, 128)
    gh.pip.wild_exprs = 0
    return gh
}

func (gh *Ghoulbert) AddVar(v *Variable, varmap map[*Atom] *IVar) *IVar {
    j := len(gh.scratch_vars)
    if j == cap(gh.scratch_vars) {
        newscratch := make([]*Variable, j+1, 2*j)
        copy(newscratch, gh.scratch_vars)
        gh.scratch_vars = newscratch
    } else {
        gh.scratch_vars = gh.scratch_vars[0 : j+1]
    }
    iv := &IVar{v.kind, j}
    varmap[v.name] = iv
    gh.scratch_vars[j] = v
    return iv
}

// Convert syntax 'syn' to an Expression, checking kinds and updating varmap
// and gh.scratch_vars at the same time.  Grows scratch_vars if necessary.
// Returns nil if unsuccessful.
//
// TODO: we need to consider overloading term operators consistent with
// the subkind mechanism. Consdier the case 'subkind (set class)'.
// Given a term 'term (class (op class class))' we might also want to introduce
// a term 'term (set (op set set))' with the same 'op', indicating that
// when the arguments of 'op' are in fact of kind 'set', the result of 'op'
// is also of kind set.  For now, we would require introducing a differently
// named term to deal with this signature change, and have to derive theorems
// stating that the values are the same when restricted to the narrower
// argument kinds...

func (gh *Ghoulbert) MakeExpr(syn SyntaxItem, varmap map[*Atom] *IVar) Expression {
    var found bool

    atom := syn.asAtom()

    if atom != nil {
        var v *Variable
        iv, found := varmap[atom]
        if found {
            return iv
        } else {
            s, found := gh.syms[atom]
            if !found {
                errMsg("Unknown symbol '%s'.\n", *atom)
                return nil
            }
            v = s.asVar()
            if v == nil {
                errMsg("Symbol '%s' is not a variable.\n",
                    *atom)
                return nil
            }
            return gh.AddVar(v, varmap)
        }
    }

    // syn must be a list

    l := syn.asList()
    rem := l.head
    if rem == nil {
        errMsg("Expected term expression, but found '()'.\n")
        return nil
    }
    tname := rem.car.asAtom()
    if tname == nil {
        errMsg("Expected term identifier, but found '%s'.\n", rem.car)
        return nil
    }
    t, found := gh.terms[tname]
    if !found {
        errMsg("Unknown term identifier '%s'.\n", *tname)
        return nil
    }
    argkinds := t.arg_kinds()
    nargs := len(argkinds)
    if l.length != nargs+1 {
        errMsg("Term '%s' requires %d arguments, but found %d\n",
            tname, nargs, l.length-1)
        return nil
    }
    texpr := &TermExpr{t, make([]Expression, nargs)}

    j := 0
    for rem = rem.cdr; rem != nil; rem = rem.cdr {
        e := gh.MakeExpr(rem.car, varmap)
        if e == nil {
            errMsg("... in '%s'\n", rem.car)
            return nil
        }
        ke := e.kind_of()
        if !ke.isSubkindOf(argkinds[j]) {
            errMsg("In term %s argument %d, expected kind %s but found %s\n",
                *tname, j, argkinds[j].name, ke.name)
            return nil
        }
        texpr.args[j] = e
        j++
    }
    return Expression(texpr)
}

func (gh *Ghoulbert) DvarsAdd(stmt *Statement, varmap map[*Atom] *IVar, dvarl *List) bool {

    var j int = 0
    var varsets [][]uint32
    allvars := len(varmap)
    bmaplen := (allvars + 31) / 32
    var varset_all []uint32 = nil
    if cap(gh.scratch_bmap) < bmaplen {
        gh.scratch_bmap = make([]uint32, bmaplen)
        varset_all = gh.scratch_bmap
    } else {
        varset_all = gh.scratch_bmap[0:bmaplen]
        for j = 0; j < bmaplen; j++ {
            varset_all[j] = 0
        }
    }
    num_dvls := dvarl.length
    if cap(gh.scratch_varsets) < num_dvls {
        varsets = make([][]uint32, num_dvls)
        for j = range gh.scratch_varsets {
            varsets[j] = gh.scratch_varsets[j]
        }
        gh.scratch_varsets = varsets
    } else {
        varsets = gh.scratch_varsets[0:num_dvls]
    }

    ix := 0
    // Handle distinct variables conditions
    for rem := dvarl.head; rem != nil; rem = rem.cdr {
        dvl := rem.car.asList()
        var varset_this []uint32 = nil
        if dvl == nil {
            errMsg("Bad distinct variables list '%s'\n", rem.car)
            return false
        }
        if cap(varsets[ix]) < bmaplen {
            varset_this = make([]uint32, bmaplen)
            varsets[ix] = varset_this
        } else {
            varset_this = varsets[ix][0:bmaplen]
            varsets[ix] = varset_this
            // Clear varset_this
            for j = range varset_this {
                varset_this[j] = 0
            }
        }
        // Ensure:
        // -- each item on the list is a known variable
        //    occurring in the hypotheses or conclusions
        // -- no variable occurs more than once in the list
        // -- at least two variables occur on the list
        for dvi := dvl.head; dvi != nil; dvi = dvi.cdr {
            vname := dvi.car.asAtom()
            if vname == nil {
                errMsg("Bad distinct variable item %s\n",
                    dvi.car)
                return false
            }
            iv, found := varmap[vname]
            if !found {
                // continue
                errMsg("%s is not a variable occurring in the hypotheses or conclusions of the assertion.\n", dvi.car)
                return false
            }
            j := iv.index
            jx := j >> 5
            var mask uint32 = 1 << (uint32(j) & 31)
            if varset_this[jx]&mask != 0 {
                errMsg("Duplicate distinct variable %s\n", vname)
                return false
            }
            varset_this[jx] |= mask
        }
        if dvl.length < 2 {
            errMsg("Too few variables in distinct variables list %s",
                dvl)
        }
        // varset_all |= varset_this
        for j = range varset_all {
            varset_all[j] |= varset_this[j]
        }
        ix++
    }

    // Count the number of variables taking part in distinct
    // variables conditions
    ix = 0
    for _, bits := range varset_all {
        for bits != 0 {
            bits &= (bits - 1)
            ix++
        }
    }
    // Number of unordered pairs of such variables:
    npairs := ix * (ix - 1) / 2
    stmt.dv_vars = make([]int, ix)
    stmt.dv_bits = make([]uint32, (npairs+31)/32)

    // Set stmt.dv_vars
    ix = 0
    for j = 0; j < allvars; j++ {
        if varset_all[j>>5]&(1<<uint32(j&31)) != 0 {
            stmt.dv_vars[ix] = j
            ix++
        }
    }

    // Set stmt.dv_bits
    // When 0 <= u < v < ix=len(stmt.dv_vars) and the bits for variables
    // stmt.dv_vars[u] and stmt.dv_vars[v] are both set in some
    // varsets[j], 0 < j < num_dvls, we set bit v*(v-1)/2 + u in stmt.dv_bits.
    //
    // u   v   bit   v*(v-1)/2 + u
    // 0   1     0        0
    // 0   2     1        1
    // 1   2     2        2
    // 0   3     3        3
    // 1   3     4        4
    // 2   3     5        5
    // ...

    base := 0
    for v := 1; v < ix; v++ {
        v1 := stmt.dv_vars[v]
        for u := 0; u < v; u++ {
            v2 := stmt.dv_vars[u]
            for j = 0; j < num_dvls; j++ {
                if varsets[j][v2>>5]&(1<<uint32(v2&31)) != 0 &&
                    varsets[j][v1>>5]&(1<<uint32(v1&31)) != 0 {
                    stmt.dv_bits[base>>5] |=
                        (1 << uint32(base&31))
                }
            }
            base++
        }
    }

    return true
}

func ExactMatch(expr1 Expression, expr2 Expression) bool {
    v1 := expr1.asIVar()
    v2 := expr2.asIVar()
    if v1 != nil {
        // These IVars() belong to the same theorem in progress;
        // index equality also implies kind equality.
        if v2 == nil || v1.index != v2.index {
            return false
        }
        return true
    } else if v2 != nil {
        return false
    }
    t1 := expr1.asTermExpr()
    t2 := expr2.asTermExpr()
    if t1.term != t2.term {
        return false
    }
    for j, subt1 := range t1.args {
        if !ExactMatch(subt1, t2.args[j]) {
            return false
        }
    }
    return true
}

// Match proof-stack expression 'expr' against statement hypothesis
// expression 'hyp'. subst lists the substitutions so far for the variables
// of the statement being applied.
// Note that subst[j] is nil if vars[j] has not yet been substituted.
// This function modifies subst.
// Returns true if match succeeds, false otherwise.
func MatchExpr(expr Expression, hyp Expression, subst []Expression) bool {
    v := hyp.asIVar()
    if v != nil {
        se := subst[v.index]
        if se != nil {
            return ExactMatch(expr, se)
        }
        k := expr.kind_of()
        if !k.isSubkindOf(v.kind) {
            return false
        }
        subst[v.index] = expr
        return true
    }
    // hyp is a termExpr. expr must be also, and the expressions must
    // match.
    te := hyp.asTermExpr()
    ete := expr.asTermExpr()
    if ete == nil {
        return false
    }
    // Note, term equality implies the argument numbers and kinds match;
    // that checking is done when the expressions are constructed from
    // syntax.
    if te.term != ete.term {
        return false
    }
    for j, subExp := range te.args {
        if !MatchExpr(ete.args[j], subExp, subst) {
            return false
        }
    }
    return true
}

type Environ struct {
    // substitutions for definition non-dummies at this level
    subst   []Expression
    // map definition dummies at this level to top-level variables
    dummymap []int
    up *Environ     // parent environment
}


// Check if the theorem variable with index ix occurs in the expression
// expr, substituted according to the environment env.
func OccursIn(ix int, expr Expression, env *Environ) bool {
    te := expr.asTermExpr()
    if te != nil {
        for _, e := range te.args {
            if OccursIn(ix, e, env) {return true}
        }
        return false
    }
    // expr is an IVar
    v := expr.asIVar()
    if env != nil {
        vix := v.index
        if vix < len(env.subst) {
            return OccursIn(ix, env.subst[vix], env.up)
        }
        // TODO: is this right?
        if env.dummymap[vix] >= 0 && vix == ix { return true }
        return false
    }
    return (v.index == ix)
}

// Match proof-stack remnant expression 'expr' against expected conclusion
// expression (or sub-expression) 'conc'. Expand definitions in expected
// conclusion to match as necessary, checking variable usage restrictions.
//
// This is probably the trickiest function in the whole program.
//
// env is non-nil if conc is below a definition RHS (definiens); in that case,
// the length of env.subst is the number of argument variables occurring in
// the definiens; and the length of env.dummymap
// Returns true if match succeeds, false otherwise.
// Note that this function may modify the target of a non-null 'env'
// passed to it.
func MatchExpand(expr Expression, conc Expression, env *Environ) bool {

    v := conc.asIVar()
    if v != nil {
        if env != nil {
            ix := v.index
            if ix < len(env.subst) {
                // v is a definition argument variable, find its substitution
                vv := env.subst[ix] // vv is non-nil
                // match expr against vv with parent environment
                return MatchExpand (expr, vv, env.up)
            }

            // v corresponds to a definition dummy. expr must be
            // a variable to match.

            w := expr.asIVar()
            if w == nil { return false }

            ix -= len(env.subst)
            jx := env.dummymap[ix]
            wix := w.index
            if jx >= 0 {
                // v is already mapped, must match exactly.
                if wix != jx { return false }
                return true
            }

            // v is a definition dummy that hasn't been matched yet.
            // The variable w must be distinct from any variable
            // passed down via the explicit definition term
            // arguments, and from any other dummy variable of
            // the current definition expansion.  We also check
            // that the kinds of the definition dummy and the
            // matching variable are _equivalent_. (TODO: could we
            // get by with a subkind relation in one direction?)

            if !v.kind.IsEquivalentTo(w.kind) { return false }

            for _, n := range env.dummymap {
                if n >= 0 && n == wix { return false }
            }

            for _, e := range env.subst {
                if e != nil && OccursIn(wix, e, env.up) {
                    return false
                }
            }
            env.dummymap[ix] = wix
            return true
        }
        w := expr.asIVar()
        if w == nil { return false }
        if v.index != w.index { return false }
        return true;
    }
    // conc is a termExpr. Since we restrict every definiens to be a
    // term expresion, expr must be a termExpr also even if conc is a
    // definition term. Unless conc is a definition term, the two terms
    // must be the same.
    te := conc.asTermExpr()
    ete := expr.asTermExpr()
    if ete == nil { return false }

    // Note, term equality implies the argument numbers and kinds match;
    // that checking is done when the expressions are constructed from
    // syntax.  If the terms match, we don't have to expand conc,
    // and the arguments should match also.
    if te.term == ete.term {
        for j, subExp := range te.args {
            if !MatchExpand(ete.args[j], subExp, env) {
                return false
            }
        }
        return true
    }

    dt := te.term
    if dt.expr == nil { return false }  // not a definition

    var dmap []int
    if dt.nDummies != 0 {
        dmap = make([]int, dt.nDummies)
    }

    return MatchExpand(expr, dt.expr, &Environ{te.args, dmap, env})
}

func SubstExpr(conc Expression, subst []Expression) Expression {
    v := conc.asIVar()
    if v != nil {
        return subst[v.index]
    }
    te := conc.asTermExpr()
    nargs := len(te.args)
    args := make([]Expression, nargs)
    for j, sub := range te.args {
        args[j] = SubstExpr(sub, subst)
    }
    return &TermExpr{te.term, args}
}

func GetVars(expr Expression, bmap []uint32) {

    v := expr.asIVar()
    if v != nil {
        j := v.index
        bmap[j>>5] |= (1 << (uint32(j) & 31))
        return
    }
    te := expr.asTermExpr()
    for _, arg := range te.args {
        GetVars(arg, bmap)
    }
}

// Check the distinct variables conditions for an application of stmt
// in a proof in progress.
func (pip *Pip) DvCheck(stmt *Statement) bool {
    var j int
    gh := pip.gh

    thm_vars := len(pip.varmap)

    ndv_vars := len(stmt.dv_vars)

    if len(gh.dv_bmaps) < ndv_vars {
        new_dv_bmaps := make ([][]uint32, ndv_vars + 8)
        copy(new_dv_bmaps, gh.dv_bmaps)
        gh.dv_bmaps = new_dv_bmaps
    }

    bmapsize := (thm_vars + 31) / 32

    for j = 0; j < ndv_vars; j++ {
        if cap(gh.dv_bmaps[j]) < bmapsize {
            gh.dv_bmaps[j] = make([]uint32, bmapsize * 2)
        } else {
            for ix := 0; ix < bmapsize; ix++ {
                gh.dv_bmaps[j][ix] = 0
            }
        }
        vj := stmt.dv_vars[j]
        GetVars(pip.subst[vj], gh.dv_bmaps[j])
        /*
        errMsg ("dv_bmaps[%d] is:", j)
        for ix := 0; ix < bmapsize; ix++ {
            errMsg (" 0x%x", gh.dv_bmaps[j][ix])
        }
        errMsg ("\n")
        */
    }

    // # vars in hypotheses or conclusions of theorem being proven
    allvars := len(pip.vars)
    // errMsg ("thm_vars=%d, allvars=%d\n", thm_vars, allvars)

    base := 0
    for j = 1; j < ndv_vars; j++ {
        for k := 0; k < j; k++ {
            // skip pairs that are not required to be distinct
            bit := base + k
            if stmt.dv_bits[bit>>5] & (1<<uint32(bit&31)) == 0 { continue }

            // Check for distinct variables violation
            for ux := 0; ux < bmapsize; ux++ {
                if gh.dv_bmaps[j][ux] & gh.dv_bmaps[k][ux] != 0 {
                    // TODO - say more about what variables
                    // caused the violation
                    errMsg("Distinct variables violation\n")
                    return false
                }
            }
            // Record all pairs of thm distinct variables in pip.dv_vars.
            // Only record for variables occurring in hypotheses or
            // conclusions; dummy variables are treated as automatically
            // distinct.

            bits_l := gh.dv_bmaps[j][0]
            for l := 0; l < allvars; {
                // errMsg ("bits_l=0x%x\n", bits_l);
                if bits_l == 0 {
                    l = (l + 32) & (^31)
                    bits_l = gh.dv_bmaps[j][l>>5]
                    continue
                }
                for (bits_l & 1) == 0 {
                    bits_l >>= 1
                    l++
                }
                if l >= allvars { break }
                bits_m := gh.dv_bmaps[k][0]
                for m := 0; m < allvars; {
                    // errMsg ("bits_m=0x%x\n", bits_m);
                    if bits_m == 0 {
                        m = (m + 32) & (^31)
                        bits_m = gh.dv_bmaps[k][m>>5]
                        continue
                    }
                    for (bits_m & 1) == 0 {
                        bits_m >>= 1
                        m++
                    }
                    if m >= allvars { break }
                    var bit int
                    if m < l {
                        bit = l * (l - 1) / 2 + m
                    } else {
                        bit = m * (m - 1) / 2 + l
                    }
                    // errMsg ("DvCheck: adding (%d, %d) bit %d for %s\n", l, m, bit, stmt.name)
                    pip.dv_pairs[bit>>5] |= 1<<uint32(bit&31)

                    bits_m >>= 1
                    m++
                }
                bits_l >>= 1
                l++
            }
        }
        base += j
    }
    return true
}

// Returns: 0 OK
//          1 syntax error
//        < 0 some other error

func (gh *Ghoulbert) ThmCmd(l *List) int {
    if l == nil || l.length != 5 {
    thm_syntax:
        return 1
    }
    rem := l.head
    thname := rem.car.asAtom()
    if thname == nil {
        goto thm_syntax
    }
    rem = rem.cdr
    dvarl := rem.car.asList()
    if dvarl == nil {
        goto thm_syntax
    }
    rem = rem.cdr
    hypl := rem.car.asList()
    if hypl == nil {
        goto thm_syntax
    }
    rem = rem.cdr
    concl := rem.car.asList()
    if concl == nil {
        goto thm_syntax
    }
    rem = rem.cdr
    proofl := rem.car.asList()
    if proofl == nil {
        goto thm_syntax
    }

    gh.pip.thm_name = thname

    s, found := gh.syms[thname]
    if found {
        what := "A variable"
        if s.asStmt() != nil {
            what = "An assertion"
        }
        errMsg("%s with name %s already exists.\n",
            what, *thname)
        return -1
    }

    // varmap maps variable names to variable indices for this
    // theorem
    varmap := make(map[*Atom] *IVar)
    gh.scratch_vars = gh.scratch_vars[0:0]

    hyps := make([]Expression, hypl.length)
    hypnames := make([]*Atom, hypl.length)
    hypmap := make(map[*Atom]int, hypl.length)

    j := 0
    for rem = hypl.head; rem != nil; rem = rem.cdr {
        hpair := rem.car.asList()
        if hpair == nil || hpair.length != 2 {
        thm_hpair_syntax:
            errMsg("Bad named hypothesis '%s'\n", rem.car)
            goto thm_syntax
        }
        hypnam := hpair.head.car.asAtom()
        if hypnam == nil {
            goto thm_hpair_syntax
        }
        _, found = hypmap[hypnam]
        if found {
            errMsg("Duplicate hypothesis name '%s'\n", hypnam)
            goto thm_syntax
        }
        hypmap[hypnam] = j
        hypnames[j] = hypnam
        e := gh.MakeExpr(hpair.head.cdr.car, varmap)
        if e == nil {
            errMsg("Bad expression %s\n", rem.car)
            return -1
        }
        hyps[j] = e
        j++
    }
    hypvars := len(varmap)

    concs := make([]Expression, concl.length)
    j = 0
    for rem = concl.head; rem != nil; rem = rem.cdr {
        e := gh.MakeExpr(rem.car, varmap)
        if e == nil {
            errMsg("Bad expression %s\n", rem.car)
            return -1
        }
        concs[j] = e
        j++
    }
    allvars := len(varmap)
    vars := make([]*Variable, allvars)
    copy(vars, gh.scratch_vars)

    thm := new(Theorem)
    thm.name = thname
    thm.vars = vars
    thm.wild_vars = allvars - hypvars
    thm.hyps = hyps
    thm.concs = concs
    thm.dv_vars = nil
    thm.dv_bits = nil

    thm.hypnames = hypnames

    // Add the provided DV conditions. Do this before adding any dummy vars
    // from the proof.
    if dvarl.head != nil {
        if !gh.DvarsAdd(&thm.Statement, varmap, dvarl) {
            return -1
        }
    }

    pip := &gh.pip
    pip.Init(vars, hypmap, varmap)

    pairs := allvars * (allvars - 1) / 2
    bsize := (pairs + 31)/32

    if len(pip.dv_pairs) < bsize {
        pip.dv_pairs = make([]uint32, bsize)
    } else {
        for j = 0; j < bsize; j++ { pip.dv_pairs[j] = 0 }
    }

    for rem = proofl.head; rem != nil; rem = rem.cdr {
        pfa := rem.car.asAtom()
        if pfa != nil {
            // check first for a hypothesis name reference
            j, found = hypmap[pfa]
            if found {
                if pip.wild_exprs != 0 {
                    errMsg("Cannot apply hypothesis (%s) with non-empty wild expression stack.\n", pfa)
                    return -1
                }
                pip.Push(thm.hyps[j])
                continue
            }
            // Now check for a variable ocurring in the hypotheses
            // or conclusions
            iv, found := varmap[pfa]
            if found {
                pip.PushWild(iv)
                continue
            }
            // General variable or stmt
            s, found = gh.syms[pfa]
            if !found {
                errMsg("Proof step is unknown symbol '%s'\n",
                    pfa)
                return -1
            }
            v := s.asVar()
            if v != nil {
                // A new proof dummy variable. Add it to varmap and 
                // gh.scratch_vars.
                iv := gh.AddVar(v, varmap)
                pip.PushWild(iv)
                continue
            }

            stmt := s.asStmt() // must be non-nil
            if !pip.Apply(stmt) { return -1 }
            continue
        }

        // rem.car is a list, and the proof step is a wild expression
        e := gh.MakeExpr(rem.car, varmap)
        if e == nil {
            errMsg("Bad expression proof step '%s'\n", rem.car)
            return -1
        }
        pip.PushWild(e)
    }

    // Check that no wild expressions remain on the stack at the
    // end of the proof.
    if pip.wild_exprs != 0 {
        errMsg("Wild expressions remain at the end of the proof.\n")
        return -1
    }

    // Check that the conclusions are as claimed, expanding definitions
    if len(pip.pf_stack) != len(thm.concs) {
        errMsg("Wrong number of conclusions on proof stack -- " +
               "expected %d but %d remain\n",
               len(thm.concs), len(pip.pf_stack))
        return -1
    }
    for j, exp := range thm.concs {
        if !MatchExpand(pip.pf_stack[j], exp, nil) {
            errMsg("Proven expression does not match expected conclusion %d\n",
                   j)
            return -1
        }
    }

    // Check that all the needed DV conditions were provided.
    base := 0
    ix := 1
    ux := 0
    fail := false
    var vx, bitn int

    for j := 0; j < bsize; j++ {
        bits := pip.dv_pairs[j]
        // errMsg (": bits=0x%x\n", bits)
        if bits == 0 { continue }
        for bit := j * 32; bits != 0; bit++ {
            if bits & 1 != 0 {
                for base + ix <= bit {
                    base = base + ix
                    ix++
                }
                jx := bit - base
                // errMsg ("Z: ix=%d, jx=%d\n", ix, jx)
                // check for existence of DV (ix jx)
                l := len(thm.dv_vars)
                for ux = 0; ux < l; ux++ {
                    if thm.dv_vars[ux] >= ix { break }
                }
                if ux == l || thm.dv_vars[ux] != ix { goto missing_dv }

                for vx = 0; vx < l; vx++ {
                    if thm.dv_vars[vx] >= jx { break }
                }

                if vx == l || thm.dv_vars[vx] != jx { goto missing_dv }

                bitn = ux * (ux - 1) / 2 + vx
                if thm.dv_bits[bitn>>5] & (1<<uint32(bitn&31)) == 0 {
missing_dv:
                    if !fail {
                        errMsg ("Missing distinct variables conditions:\n")
                        fail = true
                    }
                    // errMsg (" ix=%d, jx=%d ", ix, jx)
                    errMsg ("  (%s %s)", vars[ix].name, vars[jx].name)
                }
            }
            bits >>= 1
        }
    }

    if fail { errMsg ("\n"); return -1 }

    // Check that no excess DV conditions were provided.
    base = 0
    b1 := 0    
    for ux = 1; ux < len(thm.dv_vars); ux++ {
        ix = thm.dv_vars[ux]
        base = ix * (ix - 1)/2
        for vx = 0; vx < ux; vx ++ {
            bit := b1 + vx
            if thm.dv_bits[bit>>5] & (1<<uint32(bit&31)) == 0 { continue }
            jx := thm.dv_vars[vx]
            bit2 := base + jx
            if pip.dv_pairs[bit2>>5] & (1<<uint32(bit2&31)) == 0 {
                if !fail {
                    errMsg ("Excess distinct variables conditions:\n")
                    fail = true
                }
                errMsg (" (%s %s)", vars[ix].name, vars[jx].name)
                // thm.dv_bits[bit>>5] &^= (1<<uint32(bit&31))
            }
        }
        b1 += ux
    }

    if fail { errMsg ("\n"); return -1 }

    // Add theorem
    gh.syms[thname] = thm

    /*
    space := ""
    b1 = 0
    fmt.Printf("thm (%s (", thname)
    for ux = 1; ux < len(thm.dv_vars); ux++ {
        ix = thm.dv_vars[ux]
        for vx = 0; vx < ux; vx++ {
            bit := b1 + vx
            if thm.dv_bits[bit>>5] & (1<<uint32(bit&31)) == 0 { continue }
            jx := thm.dv_vars[vx]
            fmt.Printf("%s(%s %s)", space, vars[jx].name, vars[ix].name)
            space = " "
        }
        b1 += ux
    }
    fmt.Printf(") %s %s %s)\n", hypl, concl, proofl)
    */

    if gh.verbose != 0 {
        fmt.Printf("thm %s\n", thname)
    }
    return 0
}

func DefJustMatch(proto Expression, expr Expression, 
                  nargs int, fwd_map []int) bool {

    // errMsg("proto=%s, expr=%s, nargs=%d, fwd_map=%v\n",
    //        proto, expr, nargs, fwd_map)
    pte := proto.asTermExpr()
    if pte != nil {
        te := expr.asTermExpr()
        if te == nil { return false }
        if pte.term != te.term { return false }
        for j, arg := range pte.args {
            if !DefJustMatch(arg, te.args[j], nargs, fwd_map) { return false }
        }
        return true
    }
    piv := proto.asIVar()  // must be an IVar
    iv := expr.asIVar()
    if iv == nil { return false }
    if piv.index < nargs {
        // nondummy variables must match exactly
        if iv.index != piv.index { return false }
        return true
    }
    // Note, nargs <= piv.index < nargs + len(fwd_map).
    // Both piv and iv must be dummy variables to match. Also, iv must
    // not be one of the dummies in the original definiens.
    if iv.index < nargs + len(fwd_map) { return false }

    // check if this dummy position is already matched
    x := fwd_map[piv.index - nargs]
    if x >= 0 {
        // yes it was; match must be the same this time
        if x != iv.index { return false }
        return true
    }

    // Not matched yet.
    // variable kinds must be equivalent (not just subkind) for dummy match
    if !piv.kind.IsEquivalentTo(iv.kind) { return false }

    // iv must not have been matched previously.
    for _, x = range fwd_map {
        // note iv.index >= 0, so OK if x == -1 here
        if x == iv.index { return false }
    }
    // record match
    fwd_map[piv.index - nargs] = iv.index
    return true    
}

func (gh *Ghoulbert) Command(cmd *Atom, arg SyntaxItem) bool {
    // All of the commands currently expect *List argument.
    l := arg.asList()
    if cmd == &gh.cmds.thm {
        gh.pip.thm_name = nil
        gh.pip.vars = nil
        ret := gh.ThmCmd(l)
        if ret == 0 {
            // return true below
        } else if ret == 1 {
            errMsg("Expected 'thm (NAME ((DVAR ...) ...) ((HYPNAME HYP) ...) (CONC ...) (STEP ...))' but found\n '%s'\n", arg)
            return false
        } else {
            errMsg ("Proving theorem %s ...\n", gh.pip.thm_name)
            if gh.pip.vars != nil {gh.pip.Show()}
            return false
        }
    } else if cmd == &gh.cmds.stmt || cmd == &gh.cmds.equiv {
        if l == nil || l.length != 4 {
        stmt_syntax:
            if cmd == &gh.cmds.equiv {
                errMsg("Expected 'equiv (NAME ((DVAR ...) ...) (HYP ...) (EXPR1 EXPR2))' but found\n '%s'\n", arg.String())
            } else {
                errMsg("Expected 'stmt (NAME ((DVAR ...) ...) (HYP ...) (CONC ...))' but found\n '%s'\n", arg.String())
            }
            return false
        }
        rem := l.head
        sname := rem.car.asAtom()
        if sname == nil {
            goto stmt_syntax
        }
        rem = rem.cdr
        dvarl := rem.car.asList()
        if dvarl == nil {
            goto stmt_syntax
        }
        rem = rem.cdr
        hypl := rem.car.asList()
        if hypl == nil {
            goto stmt_syntax
        }
        rem = rem.cdr
        concl := rem.car.asList()
        if concl == nil {
            goto stmt_syntax
        }
        if cmd == &gh.cmds.equiv && concl.length != 2 {
            goto stmt_syntax
        }
        s, found := gh.syms[sname]
        if found {
            what := "A variable"
            if s.asStmt() != nil {
                what = "An assertion"
            }
            errMsg("%s with name %s already exists.\n",
                what, *sname)
            return false
        }
        // varmap maps variable names to variable indices for this
        // theorem
        varmap := make(map[*Atom] *IVar)
        gh.scratch_vars = gh.scratch_vars[0:0]
        hyps := make([]Expression, hypl.length)
        j := 0
        for rem = hypl.head; rem != nil; rem = rem.cdr {
            e := gh.MakeExpr(rem.car, varmap)
            if e == nil {
                errMsg("Bad expression %s\n", rem.car)
                return false
            }
            hyps[j] = e
            j++
        }
        hypvars := len(varmap)
        concs := make([]Expression, concl.length)
        j = 0
        for rem = concl.head; rem != nil; rem = rem.cdr {
            e := gh.MakeExpr(rem.car, varmap)
            if e == nil {
                errMsg("Bad expression %s\n", rem.car)
                return false
            }
            concs[j] = e
            j++
        }
        allvars := len(varmap)
        vars := make([]*Variable, allvars)
        copy(vars, gh.scratch_vars)
        stmt := &Statement{sname, vars, allvars - hypvars,
            hyps, concs, nil, nil, cmd == &gh.cmds.equiv}
        if dvarl.head != nil {
            if !gh.DvarsAdd(stmt, varmap, dvarl) {
                return false
            }
        }
        gh.syms[sname] = stmt
        if gh.verbose != 0 {
            fmt.Printf("%s %s\n", cmd, sname)
        }

    } else if cmd == &gh.cmds.def {
        if l == nil || l.length < 2 || l.length > 3 {
        def_syntax:
            errMsg(
                "Expected 'def ((DEFNAME ARGVAR ...) TERMEXPR [DEFPROOF])'.\n")
            return false
        }
        rem := l.head
        defl := rem.car.asList()  // definiendum
        nargs := defl.length - 1
        if defl == nil || nargs < 0 { goto def_syntax }
        dname := defl.head.car.asAtom()
        if dname == nil { goto def_syntax }

        // We require that the definiens be a term expression, not a variable.
        // This is to prevent defining, say, def ((ident x) x) and then
        // using expressions like (A. (ident x) ph).  They are probably not
        // harmful, but are ugly.
        rem = rem.cdr
        rhsl := rem.car.asList()
        if rhsl == nil { goto def_syntax }
        rem = rem.cdr

        _, found := gh.terms[dname]
        if found {
            errMsg ("A term of name %s already exists.\n", *dname)
            return false
    	}

        argkinds := make([]*Kind, nargs)
        varmap := make(map[*Atom] *IVar, nargs + 1)
        gh.scratch_vars = gh.scratch_vars[0:0]

        j := 0
        for varl := defl.head.cdr; varl != nil; varl = varl.cdr {
            vname := varl.car.asAtom()
            if vname == nil { goto def_syntax }

            _, found := varmap[vname]
            if found {
                errMsg ("Repeated definition argument '%s'\n", *vname)
                return false
            }

            s, found := gh.syms[vname]
            if !found {
                errMsg ("Unknown variable '%s'\n", vname)
                return false
            }
            v := s.asVar()
            if v == nil {
                errMsg ("Symbol '%s' is not a variable.\n", s.name_of())
                return false
            }

            gh.AddVar (v, varmap)
            argkinds[j] = v.kind
            j++
        }

        e := gh.MakeExpr(rhsl, varmap)
        if e == nil {
            errMsg("Invalid definiens expression '%s'\n", rhsl)
            goto def_syntax
        }

        // Check that every argument variable of the definiendum occurs
        // in the definiens

        for j = 0; j < nargs; j++ {
            if !OccursIn(j, e, nil) {
                errMsg ("Definition '%s' argument '%s' does not appear in the definiens.\n", dname, gh.scratch_vars[j].name)
                return false
            }
        }

        k := e.kind_of()
        d := &Term{k, dname, argkinds, e, len(varmap) - nargs}

        // If the definiens has dummy variables, check equivalence proof

        if d.nDummies != 0 {
            if rem == nil || rem.car.asList() == nil {
                errMsg("The definition '%s' has dummy variables, and " +
                       "requires an equivalence proof.\n", dname)
                return false
            }
            // TODO: set up for proof. Note, a definition proof has
            // no hypotheses, must end with an equivalence statement,
            // with exactly two 'conclusion' expressions left on the proof
            // stack.
            // The first of those expressions must exactly match the definiens.
            // The second must be the definiens with each of its dummy
            // variables replaced with a different fresh variable of the
            // same kind.

            pip := &gh.pip
            pip.Init(gh.scratch_vars[0:nargs], nil, varmap)
            pip.allowEquiv = true

            for rem = rem.car.asList().head; rem != nil; rem = rem.cdr {
                if pip.equivDone {
                    errMsg("An equivalence statement may be applied only at" +
                           "the very end of a definition justification " +
                           "proof. But a proof step followed the " +
                           "equivalence application.")

                def_proof_fail:
                    pip.Show()
                    return false
                }
                pfa := rem.car.asAtom()
                if pfa != nil {
                    // A definition proof has no hypotheses
                    // Now check for a variable ocurring in the hypotheses
                    // or conclusions
                    iv, found := varmap[pfa]
                    if found {
                        pip.PushWild(iv)
                        continue
                    }
                    // General variable or stmt
                    s, found := gh.syms[pfa]
                    if !found {
                        errMsg("Proof step is unknown symbol '%s'\n", pfa)
                        goto def_proof_fail
                    }
                    v := s.asVar()
                    if v != nil {
                        // A new proof dummy variable. Add it to varmap and 
                        // gh.scratch_vars.
                        iv := gh.AddVar(v, varmap)
                        pip.PushWild(iv)
                        continue
                    }

                    stmt := s.asStmt() // must be non-nil
                    if !pip.Apply(stmt) { goto def_proof_fail }
                        continue
                }

                // rem.car is a list, and the proof step is a wild expression
                e := gh.MakeExpr(rem.car, varmap)
                if e == nil {
                    errMsg("Bad expression proof step '%s'\n", rem.car)
                    goto def_proof_fail
                }
                pip.PushWild(e)
            }
            if !pip.equivDone {
                errMsg("A definition justification proof must end with " +
                       "an equivalnce statement.\n")
                goto def_proof_fail
            }
            // We know pip.wild_exprs == 0 since the proof ended with
            // an equivalence statement application, which like any other
            // statement application, clears pip.wild_exprs.
            // Check that exactly two expressions remain.
            if len(pip.pf_stack) != 2 {
                errMsg("More than two expressions remain at the end of a" +
                       "definition justification proof.\n")
                goto def_proof_fail
            }
            if !ExactMatch(pip.pf_stack[0], d.expr) {
                errMsg("First definition justification conclusion does not " +
                       "exactly match definiens.\n")
                goto def_proof_fail
            }
            // The definiens has nargs non-dummy variables and d.nDummies
            // dummy variables. fwd_map maps the dummy variables in the
            // definiens to those in the second equivalence expression
            fwd_map := make([]int, d.nDummies)
            for j := 0; j < d.nDummies; j++ {
                fwd_map[j] = -1
            }
            if !DefJustMatch(d.expr, pip.pf_stack[1], nargs, fwd_map) {
                errMsg ("The second definition justification conclusion " +
                        "is not the first with the original dummy " +
                        "variables replaced by fresh dummy variables.\n")
                goto def_proof_fail
            }
        }

        gh.terms[dname] = d
        if gh.verbose != 0 {
            fmt.Printf("def %s\n", dname)
        }

    } else if cmd == &gh.cmds.variable {
        if l == nil || l.length < 1 || l.head.car.asAtom() == nil {
        var_syntax:
            errMsg(
                "Expected 'var (KINDNAME VARNAME ...)', but found '%s'\n",
                arg.String())
            return false
        }
        kname := l.head.car.asAtom()
        k, found := gh.kinds[kname]
        if !found {
            errMsg("Unknown kind '%s'\n", *kname)
        }
        for vlist := l.head.cdr; vlist != nil; vlist = vlist.cdr {
            vname := vlist.car.asAtom()
            if vname == nil {
                goto var_syntax
            }
            s, found := gh.syms[vname]
            if found {
                what := "variable"
                if s.asStmt() != nil {
                    what = "statement"
                }
                errMsg(
                    "The symbol '%s' already exists as a '%s'\n",
                    *vname, what)
                return false
            }
            gh.syms[vname] = &Variable{kind: k, name: vname}
        }
        // success, return true below
    } else if cmd == &gh.cmds.term {
        if l == nil || l.length != 2 {
        term_syntax:
            errMsg("Expected 'term (RESULTKIND (TERMSYM ARGKIND ...))' but found '%s'\n", arg.String())

            return false
        }
        kname := l.head.car.asAtom()
        if kname == nil {
            goto term_syntax
        }
        tdesc := l.head.cdr.car.asList()
        if tdesc == nil || tdesc.length < 1 {
            goto term_syntax
        }
        tname := tdesc.head.car.asAtom()
        if tname == nil {
            goto term_syntax
        }
        k, found := gh.kinds[kname]
        if !found {
            errMsg("Unknown kind %s\n", *kname)
            return false
        }
        _, found = gh.terms[tname]
        if found {
            errMsg("Term %s already exists.\n",
                *tname)
            return false
        }
        nvars := tdesc.length - 1
        argkinds := make([]*Kind, nvars)
        term := &Term{k, tname, argkinds, nil, 0}
        i := 0
        for klist := tdesc.head.cdr; klist != nil; klist = klist.cdr {
            akname := klist.car.asAtom()
            if klist == nil {
                goto term_syntax
            }
            ak, found := gh.kinds[akname]
            if !found {
                errMsg("Unknown kind %s\n", *akname)
                return false
            }
            argkinds[i] = ak
            i++
        }
        gh.terms[tname] = term

    } else if cmd == &gh.cmds.kind {
        if l == nil || l.length != 1 || l.head.car.asAtom() == nil {
            errMsg("Expected 'kind (KINDNAME)' but found '%s'\n",
                arg.String())
            return false
        }
        kname := l.head.car.asAtom()

        _, found := gh.kinds[kname]
        if found {
            errMsg("Kind '%s' already exists\n", kname)
            return false
        }
        nkinds := len(gh.kinds)
        word := nkinds / 32
        bits := make([]uint32, word+1, word+1)
        nkinds -= 32 * word
        bits[word] = 1 << uint(nkinds)
        gh.kinds[kname] = &Kind{kname, bits}
        // errMsg ("kname='%s' ", *kname)
        // for i := 0; i <= word; i++ {
        //  errMsg ("0x%x ", bits[i])
        //}
        //errMsg ("\n")
    } else if cmd == &gh.cmds.subkind {
        if l == nil || l.length != 2 {
        subkindError:
            errMsg(
                "Expected 'subkind (KIND1 KIND2)' but found '%s'\n",
                arg.String())
            return false
        }
        k1name := l.head.car.asAtom()
        k2name := l.head.cdr.car.asAtom()
        if k1name == nil || k2name == nil {
            goto subkindError
        }
        k1, found := gh.kinds[k1name]
        if !found {
            errMsg("'%s' is not a known kind.\n", string(*k1name))
            return false
        }
        k2, found := gh.kinds[k2name]
        if !found {
            errMsg("'%s' is not a known kind.\n", string(*k2name))
            return false
        }
        k2.contain(k1)
        // errMsg ("k2name='%s' ", *k2name)
        // for i := 0; i < len(k2.bits); i++ {
        //  errMsg ("0x%x ", k2.bits[i])
        // }
        // errMsg ("\n")
    } else {
        errMsg("Unknown command '%s'\n", *cmd)
        return false
    }
    return true
}

func main() {
    var item SyntaxItem
    var e SyntaxErr
    var input *os.File
    var err os.Error
    var atom *Atom

    var verbose uint

    flag.UintVar (&verbose, "v", 0, "Verbosity level.")

    flag.Parse()

    if flag.NArg() == 0 {
        input = os.Stdin
    } else {
        input, err = os.Open(flag.Arg(0), os.O_RDONLY, 0)
        if input == nil {
            errMsg("Opening '%s' for reading failed (%s).\n",
                flag.Arg(0), err.String())
            os.Exit(1)
        }
    }
    gh := NewGhoulbert()

    gh.verbose = verbose

    p := NewFileParser(input, gh.intern)

    for {
        item = GetItem(p, false)
        e = item.asError()
        if e != Syntax_OK {
            if e != Syntax_EOF {
                errMsg(
                    "At line %d, %s\n", p.line, e.String())
            }
            break
        }
        atom = item.asAtom()
        if atom == nil {
            errMsg(
                "Expected command at line %d, but found\n'%s'\n",
                p.line, item.String())
            break
        }
        // Hmm, here we assume each command has a single argument syntax item
        item = GetItem(p, false)
        e = item.asError()
        if e != Syntax_OK {
            if e == Syntax_EOF {
                errMsg("Expected command argument, found EOF at line %d\n", p.line)
            } else {
                errMsg("At line %d, %s\n", p.line, e.String())
            }
            break
        }
        // At this point we know that item is an *Atom or a *List
        if !gh.Command(atom, item) {
            errMsg("... at line %d\n", p.line)
            break
        }
        /*
        if atom != &gh.cmds.thm {
            fmt.Printf("%s %s\n", *atom, item.String())
        }
        */
    }
}
