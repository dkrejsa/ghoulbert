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
// The defthm branch of Ghoulbert is based on mix of various versions of
// the Ghilbert language, plus some changes unique to itself. 
//
//   * Inference rules may have multiple conclusions as well as multiple
//     hypotheses.
//
//   * Terms may be introduced and defined by a defthm command, which must
//     contain a proof justifying the definition (with special rules for
//     handling definition dummy variables). The only information known about
//     a defined term comes from the defthm statement, which must be expicitly
//     invoked. Defined terms occurring in later theorem conclusions are not
//     automatically matched against their expansions in the corresponding
//     remnants.
//
//   * The collection of kinds is partially ordered; some kinds can be
//     'subkinds' of other kinds. In particular, 'set' variables need not
//     have an explicit conversion to 'class' variables.
//
//   * Ghoulbert uses distinct variables a-la Metamath or the original
//     Ghilbert, and does not introduce a distinction between term variables
//     and binding variables, and does not specify explicit binding information
//     for terms. (This might change.)
//
//   * There is no distinction between interface files and proof files.
//     There is only one kind of ghoulbert file, which can contain axioms,
//     kind and term declarations as well as thm and defthm commands with
//     proofs. Although not implemented yet, an import facility will allow
//     using another verified proof file together with a mapping (Ghilbert
//     context morphism) of that file's kinds, terms, and assertions to
//     the importing context, in a way that is correctness preserving.
//
// Other experimental changes are likely to be introduced in Ghoulbert.
// The aim of this experimentation is to keep the verifier simple and general
// and useful as a base for sound logical theories while increasing the
// convenience and naturalness of proofs.

//
// Ideas for import in ghoulbert
//
// import (URL (KIND_MAP) (TERM_MAP) (ASSERTION_FILTER_MAP) (VAR_HINTS))
//
// Let's call the context with this import command A.
// URL is the URL / file location for the imported proof file B.
// (KIND_MAP) describes an injective mapping f from the kinds of B to the
// kinds of A.  The mapping must preserve the subkind relation, i.e.
// f(k1) <= f(k2) if and only if k1 <= k2, where <= represents the subkind
// representation in A or B.  The verifier checks these conditions for whatever
// kind map the import statement proposes.
//
// The default (KIND_MAP) is just (), which indicates that kinds in B should
// be mapped to identically named kinds in A.
//
// Otherwise, KIND_MAP is a sequence of items, each of which represents
// a function f : Atoms x Atoms -> Atoms x Atoms, where 'Atoms' denotes the
// set of strings that are legal Ghilbert atoms.
//
// The actual kind map is the composition of all the specified mappings,
// with mappings on the left applied first; in other words, the items form
// a pipeline.  The one-to-one condition and the subkind-preserving property
// are checked only for the whole pipeline applied to the kinds of B, not
// to the individual mappings in the pipeline (although diagnostic warnings
// may be emitted).  Each kind name k of B enters the pipeline on the
// left as the pair (k, "").  The first atom of the pair is the actual kind
// name, the second atom is called its class.
//
// Presently there are the following sorts of KIND_MAP mappings:
//
//   (trans CLASS kB1 kA1 kB2 kA2 ...)
//
// After the 'trans' literal comes an atom CLASS, followed by an alternating
// list of pairs of atoms kBj kAj.  Each of the kBj's must be different.
//
// This kind of mapping applies only to pairs in the specified class CLASS;
// pairs (k, s) where s != CLASS are preserved unchanged.  A pair (k, CLASS)
// is also preserved unchanged if k is not among the listed kBj's.  If k is
// eqaual to some kBj (and it can be equal to at most one of them
// since they are all distinct), the pair (k, CLASS) is mapped to (kAj, CLASS).
//
//   (select CLASS PAT MATCH NOMATCH)
//
// Here CLASS, PAT, MATCH, and NOMATCH, are atoms. The 'select' mapping
// affects only pairs (k, s) of class CLASS; if s is not CLASS, the pair is
// passed through unchanged. PAT is an atom that acts as a pattern matching
// against the first component k of the input pair. Characters in PAT match
// literally against characters of k, except that:
//   - The character sequence '\x' in PAT matches against a single literal
//     'x' character in k, for any character 'x' that is legal in a ghilbert
//     atom. The '\' character is said to escape the subsequent character.
//     A single literal '\' character in k may be matched by the sequence '\\'
//     in PAT.  An un-escaped '\' character is not allowed at the end of PAT.
//   - An un-escaped '*' character in PAT matches any sequence of zero or more
//     characters in k. Two consecutive un-escaped '*' characters are not
//     allowed in PAT.
//
// If in the input pair (k, CLASS), k matches PAT, the output pair is
// (k, MATCH).  If the k does not match PAT, the output pair is (k, NOMATCH).
//
// The following haskell function indicates whether 'pat' is a valid pattern
// PAT for the 'select' mapping (assuming it is a valid Ghilbert atom, and
// in particular is not empty).
//
// valid_pat :: String -> Bool
// valid_pat [] = True
// valid_pat ('\\':[]) = False
// valid_pat ('\\':c:cs) = valid_pat cs
// valid_pat ('*':'*':cs) = False
// valid_pat (c:cs) = valid_pat cs
//
// The following haskell function indicates whether the atom k matches the
// pattern pat, assuming pat is a valid pattern:
//
// match :: String -> String -> Bool
// match ('\\':c:cs) [] = False
// match ('\\':c:cs) (x:xs)
//      | c == x = match cs xs
//      | otherwise = False
// match ('*':[]) xs = True
// match ('*':c:cs) [] = False
// -- be greedy here
// match p@('*':cs) k@(x:xs) = match p xs || match cs k
// match (c:cs) [] = False
// match (c:cs) (x:xs) == c == x && match cs xs
//
// Another mapping type is 
//   (ptrans CLASS PAT RES)
// As usual, this mapping passes (k, s) through unchanged unless s = CLASS.
// PAT is a pattern as described above for the 'select' mapping type.
// (k, CLASS) also passses through this mapping unchanged if k does not match
// PAT in the sense explained above.
//
// RES is an atom that may contain special sequences "\0.", "\1.", "\2.", 
// "\3.", ..., "\1001.", ...
// (in general, "\" + n +".", where n is a decimal representation of a 
// natural number).
// A '\' character that would otherwise introduce one of these sequences
// may be escaped as '\\'. However, an unescaped '\' character that is not
// followed by '\' or a decimal digit is treated literally in RES.
//
// If k matches PAT, then the output pair is (k', CLASS), where k'
// is RES with its special sequences replaced simultaneously by certain
// strings determined in the matching process. "\0." is replaced with k
// itself. Any other special sequence "\N." is replaced with the substring
// of k that matched with the Nth unescaped '*' character in PAT, if there
// is one; otherwise "\N." is replaced with the empty string.
// It is an error if k' is the empty string. (Should we make * match one-or-
// more rather than zero-or-more?)
//
// Matching against PAT is done greedily, so that if the substrings of k
// that match against the non-escaped '*' characters in PAT could be chosen
// in more than one way, choices that assign longer strings to earlier
// '*' characters are preferred.

// We could get most of the needed functionality from a single mapping
// type (PAT RES). In PAT or RES, in any maximal substring consisting of 
// consecutive '$' characters (only), if the substring contains an odd
// number (2*n + 1) of '$' characters, the first 2*n of them match n
// literal '$' characters of the token being mapped, while the last '$'
// is 'unescaped' and matches zero or more characters from the token.
// If the substring contains an even number (2*n) of '$' characters,
// these match n literal '$' characters from the token.  We allow at most
// one unescaped '$' in PAT, and the number of unescaped '$'s in RES
// must be the same as the number in PAT; an unescaped '$' in RES is replaced
// with the sequence of characters from the token that matched the unescaped
// '$' in PAT.  This allows us to match tokens in the input stream with
// arbitrary fixed prefix and suffix, and replace the prefix and suffix
// as desired.  (We might want to disallow '$' in kind/term/variable/assertion
// identifiers... we want to reserve at least tokens starting with '$' for
// other experimental purposes.)
// For cases when we want to drop a (non-axiom) assertion from the input
// stream, we could use a special RES value of "$DROP$". Alternatively, adding
// an obscure prefix would be just as good as dropping, and would be simpler
// since we wouldn't have to worry about dropping axioms of the imported
// context.
// We could also say (PAT1 RES1 PAT2 RES2 PAT3 RES3 ...) to simplify the
// syntax a bit.

package main

import (
	"fmt"
	"os"
	"flag"
	"path"
	"path/filepath"
	"unicode"
	"unicode/utf8"
)

func errMsg(format string, args ...interface{}) {
	fmt.Fprintf(os.Stderr, format, args...)
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
		if b1&k2.bits[i] != b1 {
			return false
		}
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
		if k1.bits[i] != k2.bits[i] {
			return false
		}
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

func (k *Kind) String() string {
	return string(*k.name)
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
	expr     Expression // nil if not a definition term
	nDummies int        // 0 if not a defintion term
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
	Syntax(vars []*Variable, offset int) string
	depth() int
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

func (te *TermExpr) depth() int {
	d := 0
	for _, sub := range te.args {
		sd := sub.depth()
		if sd > d {
			d = sd
		}
	}
	return (d + 1)
}

func (te *TermExpr) Syntax(vars []*Variable, offset int) string {
	if offset < 0 {
		s := "("
		s += string(*te.term.name_of())
		for _, sub := range te.args {
			s += " "
			s += sub.Syntax(vars, offset)
		}
		s += ")"
		return s
	}
	d := te.depth()
	if d <= 2 {
		return te.Syntax(vars, -1)
	}
	// we know len(te.args) > 0, or max_depth would be 0
	s := "(" + string(*te.term.name_of()) + " "
	offset = offset + len(s)
	spacer_slc := make([]byte, offset+1)
	spacer_slc[0] = '\n'
	for ix := 0; ix < offset; ix++ {
		spacer_slc[ix+1] = ' '
	}
	spacer := string(spacer_slc)
	for ix, sub := range te.args {
		if ix != 0 {
			s += spacer
		}
		s += sub.Syntax(vars, offset)
	}
	return s + ")"
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

	// Is the statement an axiom?
	axiomatic  bool
}

type Theorem struct {
	Statement

	// Like the proof, hypnames is not really of use after the theorem
	// is proved, unless one stores the proof ...
	hypnames []*Atom // used only in theorems, nil otherwise
}


// Proof-in-Progress structure
type Pip struct {
	isDefThm   bool
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
	dv_pairs []uint32
	thm_name *Atom
}

func (pip *Pip) Init(vars []*Variable, hypmap map[*Atom]int, varmap map[*Atom]*IVar) {
	pip.isDefThm = false
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

// Create a new expression formed by simultaneously substituting
// the IVars in expression <conc> according to <subst>.
// Used to find the substitution instance of a conclusion of
// the theorem being applied which should be pushed on the proof stack.
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

func (pip *Pip) Apply(stmt *Statement) bool {

	if stmt.wild_vars != pip.wild_exprs {
		errMsg("Assertion %s requrires %d wild variables, "+
			"but %d were provided.\n",
			stmt.name, stmt.wild_vars, pip.wild_exprs)
		return false
	}

	nproven := len(pip.pf_stack) - pip.wild_exprs
	if len(stmt.hyps) > nproven {
		errMsg("Assertion %s requires %d hypotheses, but only "+
			"%d expressions are available on the proof stack.\n",
			stmt.name, len(stmt.hyps), nproven)
		return false
	}

	nsvars := len(stmt.vars)

	if nsvars > cap(pip.subst) {
		pip.subst = make([]Expression, nsvars, nsvars+8)
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
			errMsg("Assertion %s wild variable %s has kind %s "+
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

func (pip *Pip) Show() {
	l := len(pip.pf_stack)
	n := l - pip.wild_exprs
	vars := pip.gh.scratch_vars
	var jx int
	var num string
	offset := -1
	if pip.gh.pretty_print {
		offset = 0
	}
	for jx = 0; jx < n; jx++ {
		e := pip.pf_stack[jx]
		num = fmt.Sprintf("P%-2d  ", jx)
		if offset >= 0 {
			offset = len(num)
		}
		errMsg("%s%s\n", num, e.Syntax(vars, offset))
	}
	for jx < l {
		e := pip.pf_stack[jx]
		num = fmt.Sprintf("W%-2d  ", jx-n)
		if offset >= 0 {
			offset = len(num)
		}
		errMsg("%s%s\n", num, e.Syntax(vars, offset))
		jx++
	}
}

func (s *Statement) name_of() *Atom { return s.name }

func (s *Statement) asStmt() *Statement { return s }

func (s *Statement) asVar() *Variable { return nil }

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

func (iv *IVar) Syntax(vars []*Variable, offset int) string {
	return string(*vars[iv.index].name)
}

func (iv *IVar) depth() int {
	return 0
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

const (
	bufsz   = 8192
	prelude = 8
)

func NewFileParser(file *os.File, intern map[string]*Atom) *FileParser {
	if file == nil {
		return nil
	}
	return &FileParser{file, make([]byte, prelude+bufsz),
		0, 0, false, 1, make([]byte, 64), intern}
}

func (p *FileParser) Line() int {
	return p.line
}

func (p *FileParser) GetRune() (rune rune, size int) {
	var ix = p.start
	var l = p.end
	var n int = l - ix
	var err error

	for n < 4 && !p.eof {
		copy(p.buf[prelude-n:prelude], p.buf[ix:l])
		ix = prelude - n
		n, err = p.file.Read(p.buf[prelude:])
		if n < 0 {
			errMsg("GetRune: Read failed. error='%s'\n", err.Error())
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

// Token type codes
const (
	OPEN_P = iota
	CLOSE_P
	ATOM
	EOFILE
)

func (p *FileParser) GetToken() (code int, atom *Atom) {

	atomlen := 0
	var rune rune
        var size int

outer_loop:
	for {
		rune, size = p.GetRune()
		if rune == '(' {
			if atomlen != 0 {
				break
			}
			p.start += size
			return OPEN_P, nil
		}
		if rune == ')' {
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
			case '\r':
				rune, size = p.GetRune()
				if rune == '\n' {
					p.start += size
				}
				fallthrough
			case '\n':
				p.line += 1
			}
			continue
		}
		if rune == '#' {
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
				case '\r':
					rune, size = p.GetRune()
					if rune == '\n' {
						p.start += size
					}
					fallthrough
				case '\n':
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
	// Note, this conversion must generate an independent immutable instance
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
	Line() int
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
	defthm   Atom
	thm      Atom
	_import  Atom
}

// Ghoulbert state shared by all Ghoulbert contexts (proof files)
// Note at present we assume a single verifier thread, i.e. no mutual
// exclusion issues.
type GhoulbertGlobal struct {
	cmds   CommandList
	intern map[string]*Atom
	ghmap  map[string]*Ghoulbert
	opaque *TermExpr  // fake, opaque definiens expression for imported defined terms
}

func newGhoulbertGlobal() *GhoulbertGlobal {

	var glob = new(GhoulbertGlobal)

	intern := make(map[string]*Atom, 128)
	glob.cmds.kind = Atom("kind")
	glob.cmds.subkind = Atom("subkind")
	glob.cmds.variable = Atom("var")
	glob.cmds.term = Atom("term")
	glob.cmds.stmt = Atom("stmt")
	glob.cmds.thm = Atom("thm")
	glob.cmds.defthm = Atom("defthm")
	glob.cmds._import = Atom("import")
	// Hmm, consider symbol leak: if a name gets interned,
	// and then is no longer needed, how can we know when it may
	// be removed from the intern map? Maintain a reference count
	// for each name?
	intern[string(glob.cmds.kind)] = &glob.cmds.kind
	intern[string(glob.cmds.subkind)] = &glob.cmds.subkind
	intern[string(glob.cmds.variable)] = &glob.cmds.variable
	intern[string(glob.cmds.term)] = &glob.cmds.term
	intern[string(glob.cmds.stmt)] = &glob.cmds.stmt
	intern[string(glob.cmds.thm)] = &glob.cmds.thm
	intern[string(glob.cmds.defthm)] = &glob.cmds.defthm
	intern[string(glob.cmds._import)] = &glob.cmds._import
	glob.intern = intern

	glob.ghmap = make(map[string]*Ghoulbert, 10)

	glob.opaque = &TermExpr{nil, nil}

	return glob
}

func normalize(dir string) string {
	var err error
	dir1 := path.Clean(dir)
	dir2, err := filepath.Abs(dir1)
	if err != nil {
		errMsg("normalize: path.Abs(%s)\n", dir1)
		os.Exit(1)
	}
	dir3, err := filepath.EvalSymlinks(dir2)
	if err != nil {
		errMsg("normalize: path.EvalSymlinks(%s)\n", dir2)
		os.Exit(1)
	}
	return dir3
}


func (glob *GhoulbertGlobal) GhoulbertForUrl(basedir string, url string, verbose uint, pretty bool) *Ghoulbert {
	var input *os.File
	var err error
	var fullpath string
	var gh *Ghoulbert

	if url == "" {
		input = os.Stdin
		basedir = normalize(basedir)
		fullpath = path.Join(basedir,"#0")

	} else {  // TODO: handle actual URLs
		if path.IsAbs(url) {
			basedir, url = path.Split(url)
			if basedir == "" {
				basedir = "."
			}
		}
		basedir = normalize(basedir)
		fullpath = path.Join(basedir, url)
	}
	gh = glob.ghmap[fullpath]
	if gh != nil {
		if !gh.complete {
			errMsg("Recursive use of '%s'\n", fullpath)
			os.Exit(1)
		}
		return gh
	}

	if input == nil {
		input, err = os.Open(fullpath)
		if input == nil {
			errMsg("Opening '%s' for reading failed (%s).\n",
				fullpath, err.Error())
			os.Exit(1)
		}
	}

	gh = NewGhoulbert(glob, basedir, fullpath)

	gh.verbose = verbose
	gh.pretty_print = pretty

	p := NewFileParser(input, glob.intern)

	gh.ReadVerify(p)

	gh.complete = true

	// clean up parts of gh no longer needed?
	return gh
}

// Ghoulbert state specific to a particular context (proof file)
// Perhaps some more of the members here can & should be moved to
// GhoulbertGlobal, e.g. Pip, & various scratch* that are not needed
// after verification is complete.
type Ghoulbert struct {
	glob            *GhoulbertGlobal
	kinds           map[*Atom]*Kind
	syms            map[*Atom]Symbolic // variables and thm/stmt names
	terms           map[*Atom]*Term
	scratch_vars    []*Variable
	scratch_bmap    []uint32
	scratch_varsets [][]uint32
	dv_bmaps        [][]uint32
	pip             Pip
	verbose         uint
	pretty_print    bool
	basedir	        string
	fullpath	string
	complete	bool
}

func NewGhoulbert(glob *GhoulbertGlobal, basedir string, fullpath string) *Ghoulbert {
	gh := new(Ghoulbert)
	gh.glob = glob

	gh.kinds = make(map[*Atom]*Kind, 128)
	gh.syms = make(map[*Atom]Symbolic, 512)
	gh.terms = make(map[*Atom]*Term, 256)
	gh.scratch_vars = make([]*Variable, 0, 128)
	gh.scratch_bmap = make([]uint32, 2)
	gh.scratch_varsets = make([][]uint32, 16)
	gh.pip.gh = gh
	gh.pip.pf_stack = make([]Expression, 128)
	gh.pip.wild_exprs = 0
	gh.basedir = basedir
	gh.fullpath = fullpath
	gh.complete = false
	return gh
}

// This structure maintains the state of an import of one Ghoulbert file by
// another, for the duration of the import.
// To begin with, we'll follow the strategy of translating all imported
// assertions from the import context into new native assertions in the
// importing context, rather than trying to share any structure between the
// Statement objects.  This will increase memory usage for assertions by
// a factor of the number of times a given context is imported; but may
// be simpler.

// OK, this also implies that if module A imports module B and module C,
// where module C also imports module B, module A already has various
// assertions from module B when module C is imported. If an assertion
// of module C that comes from module B gets imported into module A, then
// if it has a new name in module A, it will just have essentially duplicate
// content. On the other hand, if it has the same name as an assertion
// already imported from B, the proof checker must check that the new
// assertion being imported is _equivalent_ in some appropriate sense
// to the one already visible in A.

// Or, we could simply say that if we try to import a (non-axiomatic) 
// assertion with a name that already exists in the importing context, we
// just don't import that one -- ignore it, possibly logging a warning.
// That would be simpler.

// It might be a better strategy, leading to better performance, for module
// A to import only module C, and get all the module B stuff indirectly from
// module C.

// Of course, all Axioms of an imported context must be mapped to an equivalent
// assertion (either axiomatic or already proven) in the importing context.
// (Since Axioms from the imported context must be treated differently from 
// proven theorems of the imported context, would it make sense to use a
// separate mapping for them?)

type GhImport struct {
	gh		*Ghoulbert  // The importing context
	gh_imp		*Ghoulbert  // The imported context

	kmap		map[*Kind]*Kind  // Map from kinds of gh_imp to kinds of gh
	tmap		map[*Term]*Term  // Map from terms of gh_imp to terms of gh
	vmap		map[*Variable]*Variable // Map from vars of gh_imp to vars of gh
}


func (gh *Ghoulbert) AddVar(v *Variable, varmap map[*Atom]*IVar) *IVar {
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

func (gh *Ghoulbert) MakeExpr(syn SyntaxItem, varmap map[*Atom]*IVar) Expression {
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
	return texpr
}

// Parse & check format of distinct variables list for assertion being added.
// Set stmt.dv_bits and stmt.dv_vars appropriately. Note that stmt.dv_vars
// must list the indices of variables used in the statement and occurring in the
// DV lists in increasing order of index.
// Return true for success, false for failure
func (gh *Ghoulbert) DvarsAdd(stmt *Statement, varmap map[*Atom]*IVar, dvarl *List) bool {

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
			return false
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
		return v2 != nil && v1.index == v2.index;
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
	subst []Expression
	// map definition dummies at this level to top-level variables
	dummymap []int
	up       *Environ // parent environment
}


// Record all of the IVars occurring in <exp>, each at its own index in <vect>
// This function is used to ensure that all the formal arguments of a defined
// term occur in the definiens.
func RecordVars(exp Expression, vect[]*IVar) {
	v := exp.asIVar()
	if v != nil {
		vect[v.index] = v
		return
	}
	te := exp.asTermExpr()
	for _, sub := range te.args {
		RecordVars(sub, vect)
	}
}

// This function creates a deep copy of the expression exp, which is a sub-expression of
// a defthm remnant matching the expansion of the term being defined (or part of it).
// This function updates the contents of vect, adding variables and incrementing *index
// when it does so. *index starts as the number of arguments of the definition term.
// The slice <vect> maps variable indices in the theorem environment to new IVars whose
// indices reflect the argument index or higher definition dummy variable index in the
// definition term. <vect> starts out mapping only the argument variable indices, and
// mappings for the definition dummy variables in the matching expansion are added as
// encountered.
func DefExprCopy(exp Expression, vect []*IVar, index *int,
allvars int) Expression {
	// errMsg ("exp=%v, vect=%p, index=%v, allvars=%v\n", exp, vect, index, allvars)
	v := exp.asIVar()
	if v != nil {
		w := vect[v.index]
		if w == nil {
			// All variables in the expression that are not arguments
			// of the matching definition term must be proof dummies.
			if v.index < allvars {
				errMsg("Definition dummy occurs in hypotheses or conclusions\n")
				return nil
			}
			w = &IVar{v.kind, *index}
			(*index)++
			vect[v.index] = w

		}
		return w
	}
	te := exp.asTermExpr()
	nargs := len(te.args)
	args := make([]Expression, nargs)
	cte := &TermExpr{te.term, args}
	for j, sub := range te.args {
		e := DefExprCopy(sub, vect, index, allvars)
		if e == nil {
			return nil
		}
		args[j] = e
	}
	return cte
}

// This function is called to match a conclusion <conc> of a defthm
// against the corresponding remnant expression <exp> on the proof stack.
// <dterm> is the definition term, which will be updated with the definiens
// when the match determines it.
// <vect> is updated also; it forms a scratch space reused on each occurrence
// of the definition term in a subexpression of <conc>; in each such occurrence
// all of the term arguments must be variables (and all the variables in
// any one occurrence distinct). <vect> maps the actual argument ivar index
// to a new ivar whose index is the argument index in the definition term.
// Each argument variable must occur in the matching subexpression of <exp>
// and any other variable in the matching subexpression of <exp> must be
// a proof dummy variable corresponding to a definition dummy variable.
// Returns true if the match succeeds, false otherwise.
func DefConcMatch(conc Expression, exp Expression, dterm *Term,
allvars int, vect []*IVar) bool {
	// errMsg ("conc=%v, exp=%v, dterm=%v, allvars=%v, vect=%p\n", conc, exp, dterm, allvars, vect)
	v := conc.asIVar()
	w := exp.asIVar()
	if v != nil {
		return w != nil && w.index == v.index
	} else if w != nil {
		// We don't allow definitions that expand to a variable
		errMsg("Cannot match %s against variable %s\n", conc, exp)
		return false
	}
	cte := conc.asTermExpr()
	te := exp.asTermExpr()

	if cte.term != dterm {
		// errMsg ("cte=%v, te=%v, cte.term=%p, te.term=%p\n", cte, te, cte.term, te.term)
		if cte.term != te.term {
			errMsg("Cannot match %s against expression %s\n", conc, exp)
			return false
		}
		for j, sub := range cte.args {
			// errMsg ("sub=%v, te.args[j]=%v\n", sub, te.args[j])
			if !DefConcMatch(sub, te.args[j], dterm, allvars, vect) {
				return false
			}
		}
		return true
	}

	var j int

	// cte is an occurrence of the definition term.
	// Check that all of cte's arguments are variables, and that each 
	// such variable occurs only once. Note, kind checking already occurred
	// when the conclusion was parsed.

	for j := range vect {
		vect[j] = nil
	}
	for j, sub := range cte.args {
		v = sub.asIVar()
		if v == nil {
			errMsg("Argument %s of term %s being defined is not a variable.\n", sub, cte)
			return false
		}
		if vect[v.index] != nil {
			errMsg("Repeated argument variable %s in term %s being defined.\n", v, cte)
			return false
		}
		vect[v.index] = &IVar{v.kind, j}
	}
	index := j
	e := DefExprCopy(exp, vect, &index, allvars)
	if e == nil {
		return false
	}
	if dterm.expr == nil {
		// This is the first match against the definition term.
		dterm.expr = e
		dterm.nDummies = index - j
		// Check that there are no argument variables that do not occur in the expansion.
		// (Reusing vect for a different purpose here.)
		for j = range vect {
			vect[j] = nil
		}
		RecordVars(e, vect)
		for j = range cte.args {
			if vect[j] == nil {
				errMsg("Argument #%d of defined term %s does not occur in the definiens\n",
					j, cte.term.name)
				return false
			}
		}
		return true
	}
	if ExactMatch(dterm.expr, e) {
		return true
	}

	errMsg("Two occurences of the term '%s' match non-equivalent expressions.\n", *dterm.name)
	return false
}

// Set bits in bmap corresponding to the indices of all IVars occurring
// in expr.
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
		new_dv_bmaps := make([][]uint32, ndv_vars+8)
		copy(new_dv_bmaps, gh.dv_bmaps)
		gh.dv_bmaps = new_dv_bmaps
	}

	bmapsize := (thm_vars + 31) / 32

	for j = 0; j < ndv_vars; j++ {
		if cap(gh.dv_bmaps[j]) < bmapsize {
			gh.dv_bmaps[j] = make([]uint32, bmapsize*2)
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
			if stmt.dv_bits[bit>>5]&(1<<uint32(bit&31)) == 0 {
				continue
			}

			// Check for distinct variables violation
			for ux := 0; ux < bmapsize; ux++ {
				if gh.dv_bmaps[j][ux]&gh.dv_bmaps[k][ux] != 0 {
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
				if l >= allvars {
					break
				}
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
					if m >= allvars {
						break
					}
					var bit int
					if m < l {
						bit = l*(l-1)/2 + m
					} else {
						bit = m*(m-1)/2 + l
					}
					// errMsg ("DvCheck: adding (%d, %d) bit %d for %s\n", l, m, bit, stmt.name)
					pip.dv_pairs[bit>>5] |= 1 << uint32(bit&31)

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

func (gh *Ghoulbert) ThmCmd(l *List, defthm bool) int {
	if l == nil || (!defthm && l.length < 4) || (defthm && l.length < 6) {
		return 1
	}
	rem := l.head
	thname := rem.car.asAtom()
	if thname == nil {
		return 1
	}
	rem = rem.cdr

	var kname *Atom
	var defl *List
	var nargs int
	var dname *Atom

	if defthm {
		kname = rem.car.asAtom()
		if kname == nil {
			return 1;
		}
		rem = rem.cdr

		defl = rem.car.asList() // definiendum with kinds instead of args
		if defl == nil {
			return 1
		}
		nargs = defl.length - 1
		if nargs < 0 {
			return 1
		}
		dname = defl.head.car.asAtom()
		if dname == nil {
			return 1
		}
		rem = rem.cdr
	}

	dvarl := rem.car.asList()
	if dvarl == nil {
		return 1
	}
	rem = rem.cdr

	hypl := rem.car.asList()
	if hypl == nil || (hypl.length&1) != 0 {
		return 1
	}
	rem = rem.cdr

	concl := rem.car.asList()
	if concl == nil {
		return 1
	}

	proofl := rem.cdr

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
	varmap := make(map[*Atom]*IVar)
	gh.scratch_vars = gh.scratch_vars[0:0]

	var nhyps = hypl.length / 2
	hyps := make([]Expression, nhyps)
	hypnames := make([]*Atom, nhyps)
	hypmap := make(map[*Atom]int, nhyps)

	j := 0
	for rem = hypl.head; rem != nil; rem = rem.cdr {
		hypnam := rem.car.asAtom()
		if hypnam == nil {
			errMsg("Expected hypothesis name, found '%s'\n", rem.car)
			return 1
		}
		_, found = hypmap[hypnam]
		if found {
			errMsg("Duplicate hypothesis name '%s'\n", hypnam)
			return 1
		}
		hypmap[hypnam] = j
		hypnames[j] = hypnam
		rem = rem.cdr
		e := gh.MakeExpr(rem.car, varmap)
		if e == nil {
			errMsg("Bad expression %s\n", rem.car)
			return -1
		}
		hyps[j] = e
		j++
	}
	hypvars := len(varmap)

	var k *Kind
	var argkinds []*Kind
	var dterm *Term

	if defthm {
		k, found = gh.kinds[kname]
		if !found {
			errMsg("Unknown kind %s\n", *kname)
			return -1
		}

		_, found = gh.terms[dname]
		if found {
			errMsg("A term of name %s already exists.\n", *dname)
			return -1
		}

		argkinds = make([]*Kind, nargs)
		dterm = &Term{k, dname, argkinds, nil, 0}

		j := 0
		// errMsg ("defl=%v, defl.head=%v, nargs=%v\n", defl, defl.head, nargs)
		for argkl := defl.head.cdr; argkl != nil; argkl = argkl.cdr {
			akname := argkl.car.asAtom()
			if akname == nil {
				return 1
			}

			ak, found := gh.kinds[akname]
			if !found {
				errMsg("Unknown kind '%s'\n", *akname)
				return -1
			}
			argkinds[j] = ak
			j++
		}
		// For a defthm, we need to temporarily add the new definition
		// term to gh.terms, so that it is visible when parsing the
		// conclusion(s); but we remove it during the proof proper, where
		// it must not be visible yet.

		gh.terms[dname] = dterm
	}

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

	// The variables used in the hypotheses or conclusions
	allvars := len(varmap)
	vars := make([]*Variable, allvars)
	copy(vars, gh.scratch_vars)

	if defthm {
		delete (gh.terms, dname)
	}

	thm := new(Theorem)
	thm.name = thname
	thm.vars = vars
	thm.wild_vars = allvars - hypvars
	thm.hyps = hyps
	thm.concs = concs
	thm.dv_vars = nil
	thm.dv_bits = nil
	thm.axiomatic = false

	thm.hypnames = hypnames

	// Add the provided DV conditions. Do this before adding any dummy vars
	// from the proof, since only variables occurring in the hypotheses or
	// conclusions are allowed in DV conditions.
	if dvarl.head != nil {
		if !gh.DvarsAdd(&thm.Statement, varmap, dvarl) {
			return -1
		}
	}

	pip := &gh.pip
	pip.Init(vars, hypmap, varmap)

	pairs := allvars * (allvars - 1) / 2
	bsize := (pairs + 31) / 32

	if len(pip.dv_pairs) < bsize {
		pip.dv_pairs = make([]uint32, bsize)
	} else {
		for j = 0; j < bsize; j++ {
			pip.dv_pairs[j] = 0
		}
	}

	for rem = proofl; rem != nil; rem = rem.cdr {
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
			// or conclusions, or a proof dummy variable seen earlier.
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
			if !pip.Apply(stmt) {
				return -1
			}
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

	// Check that we have the expected number of conclusions.
	if len(pip.pf_stack) != len(thm.concs) {
		errMsg("Wrong number of conclusions on proof stack -- "+
			"expected %d but %d remain\n",
			len(thm.concs), len(pip.pf_stack))
		return -1
	}

	// Check that the conclusions are as claimed.  For non-definition
	// theorems, the conclusions must be identical.  For definition theorems,
	// the conclusions must 'match' the remnant expressions.

	if defthm {
		// Criteria for good defthm conclusion(s) match:
		// -- The definition term must occur at least once in the conclusions.
		// -- The arguments of each occurrence of the definition term must
		//    be simple variables, not term expressions. [Could we weaken
		//    this to say just that for at least one occurrence of the
		//    definition term, all of the arguments are variables? Or simply that
		//    it is possible to determine a unique definiens consistent with all
		//    occurrences?]
		// -- The argument variables must all occur in the expression that the
		//    definition term occurrence substitutes for.
		// -- Any variables that occur in the expression substituted by
		//    a definition term but that are not among the definition term
		//    arguments must be proof dummies (i.e. must not occur in the
		//    hypotheses or conclusions).  Such variables will correspond to
		//    definition dummy variables.
		// -- Each occurrence of the definition term must determine an 
		//    identical [Later: consistent? unifiable?] definiens, up to 1-1
		//    consistent replacement of variables.
		//[Not this:
		// -- Definition dummy variables within the subexpression matching one
		//    occurrence of the definition term in the conclusions must be
		//    distinct from the definition dummy variables occurring in
		//    the remnant subexpression matching any other occurrence of the
		//    definition term.
		// because whether a term appears once or more than once in an
		// expression is not invariant under logical (or even definitional) 
		// equivalence: consider
		// (<-> (true) (-> ph ph)) vs. (/\ (-> (true) (-> ph ph))
		//                                 (-> (-> ph ph) (true)))
		// (But then, how can we rule out "spooky interactions at a distance"
		// between the same dummy variables in different occurrences of the
		// expanded definition term?)
		//]
		vect := make([]*IVar, len(varmap))
		for j, exp := range thm.concs {
			if !DefConcMatch(exp, pip.pf_stack[j], dterm, allvars, vect) {
				errMsg("Definition theorem proven expression\n  %s\ndoes not match expected conclusion %d\n  %s\n", pip.pf_stack[j], j, exp)
				return -1
			}
		}
		if dterm.expr == nil {
			errMsg("There were no '%s' terms found in the conclusion(s).\n",
				*dterm.name)
			return -1
		}

	} else {
		for j, exp := range thm.concs {
			if !ExactMatch(pip.pf_stack[j], exp) {
				errMsg("Proven expression\n  %s\ndoes not match expected conclusion %d\n  %s\n", pip.pf_stack[j], j, exp)
				return -1
			}
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
		// errMsg ("j=%d : bits=0x%x\n", j, bits)
		if bits == 0 {
			continue
		}
		for bit := j * 32; bits != 0; bit++ {
			if bits&1 != 0 {
				for base+ix <= bit {
					base = base + ix
					ix++
				}
				jx := bit - base
				// errMsg ("Z: ix=%d, jx=%d\n", ix, jx)
				// check for existence of DV (ix jx)
				l := len(thm.dv_vars)
				for ux = 0; ux < l; ux++ {
					if thm.dv_vars[ux] >= ix {
						break
					}
				}
				if ux == l || thm.dv_vars[ux] != ix {
					goto missing_dv
				}

				for vx = 0; vx < l; vx++ {
					if thm.dv_vars[vx] >= jx {
						break
					}
				}

				if vx == l || thm.dv_vars[vx] != jx {
					goto missing_dv
				}

				bitn = ux*(ux-1)/2 + vx
				if thm.dv_bits[bitn>>5]&(1<<uint32(bitn&31)) == 0 {
					goto missing_dv
				}
				bits >>= 1
				continue;

			missing_dv:
				if !fail {
					errMsg("Missing distinct variables conditions:\n")
					fail = true
				}
				// errMsg (" ix=%d, jx=%d ", ix, jx)
				errMsg("  (%s %s)", vars[ix].name, vars[jx].name)

			}
			bits >>= 1
		}
	}

	if fail {
		errMsg("\n")
		return -1
	}

	// Check that no excess DV conditions were provided.
	base = 0
	b1 := 0
	for ux = 1; ux < len(thm.dv_vars); ux++ {
		ix = thm.dv_vars[ux]
		base = ix * (ix - 1) / 2
		for vx = 0; vx < ux; vx++ {
			bit := b1 + vx
			if thm.dv_bits[bit>>5]&(1<<uint32(bit&31)) == 0 {
				continue
			}
			jx := thm.dv_vars[vx]
			bit2 := base + jx
			if pip.dv_pairs[bit2>>5]&(1<<uint32(bit2&31)) == 0 {
				if !fail {
					errMsg("Excess distinct variables conditions:\n")
					fail = true
				}
				errMsg(" (%s %s)", vars[ix].name, vars[jx].name)
				// thm.dv_bits[bit>>5] &^= (1<<uint32(bit&31))
			}
		}
		b1 += ux
	}

	if fail {
		errMsg("\n")
		return -1
	}

	if defthm {
		gh.terms[dname] = dterm
	}

	// Add theorem
	gh.syms[thname] = thm

	if gh.verbose != 0 {
		if defthm {
			fmt.Printf("defthm %s\n", thname)
		} else {
			fmt.Printf("thm %s\n", thname)
		}
	}
	return 0
}

type PatRep struct {
	ps  string  // prefix + suffix of pattern/replacement
	wix int     // prefix length of pattern/replacement. -1 if no wildcard.
}

func mapSyntax(arg SyntaxItem, name string) []PatRep {
	l := arg.asList()
	if l == nil || (l.length&1) != 0 {
		errMsg("%s must be a list with an even number of elements,\n", name)
		errMsg("(alternating PATTERN and REPLACEMENT atoms)\n")
		return nil
	}

	var wix int
	var word *Atom

	mvec := make([]PatRep, l.length)
	pix := 0

	for rem := l.head; rem != nil; rem = rem.cdr {
		word = rem.car.asAtom()
		if word == nil {
			errMsg("Elements of %s must be atoms.\n", name)
			return nil
		}
		// Check for at most a single undoubled '$' character
		wix = -1
		wl := len(*word)
		ps := ""
		for jx := 0; jx < wl; jx++ {
			c := (*word)[jx]
			if c != '$' { ps += string(c) ; continue }
			if jx < wl - 1 && (*word)[jx+1] == '$' {
				// doubled (quoted) '$'
				ps += string(c)
				jx++
				continue
			}
			if wix != -1 {
				// Check for "$DROP$" special case in REP
				if (pix&1) != 0 && *word == "$DROP$" {
					ps = ""
					wix = -1
					break
				}
				errMsg("More than one unquoted '$' character occurs in PATTERN or REPLACEMENT %s", word)
				return nil
			}
			wix = len(ps)
		}
		mvec[pix].ps = ps
		mvec[pix].wix = wix
		// Check that if the REPLACEMENT has a wildcard, the PATTERN
		// does too; but not vice-versa.
		if wix != -1 && (pix&1) != 0 && mvec[pix-1].wix == -1 {
			errMsg("Replacement %s has '$' but corresponding pattern does not\n", word)
			return nil
		}
		pix++
	}

	return mvec
}

// <pr> is an alternating slice of PATTERN and REPLACEMENT PatReps
// <name> is the name to be mapped according to the sequence of
// PATTERNs and REPLACEMENTs.
// Interns the resulting atom.
func (glob *GhoulbertGlobal) MapIt (pr []PatRep, name string) *Atom {

	// Ugh -- lots of strings created & destroyed; this is a garbage
	// collector workout and probably hurts performance and locality.
	npr := len(pr)
	for ix := 0; ix < npr; ix += 2 {
		pat := pr[ix]
		rep := pr[ix+1]
		wix := pat.wix
		if wix == -1 {
			if pat.ps != name { continue }
			// rep.wix == -1 also, checked in mapSyntax()
			name = rep.ps
			if name == "" { return nil }
			continue
		}
		// name must be longer than pat.ps to match.
		// (We do not allow zero-length wildcards.)
		ln := len(name)
		lp := len(pat.ps)
		if ln <= lp { continue }
		// Check that prefix and suffix of pattern match.
		nsi := ln - (lp - wix) // name suffix index
		if name[:wix] != pat.ps[:wix] { continue }
		if name[nsi:] != pat.ps[wix:] { continue }
		// OK, we match; construct the replacement name
		rwix := rep.wix
		if rwix == -1 {
			name = rep.ps  // also handles drop ("") case
			if name == "" { return nil }
		} else {
			name = rep.ps[:rwix] + name[wix:nsi] + rep.ps[rwix:]
		}
	}

	a, found := glob.intern[name]
	if found {
		return a
	}
	aa := Atom(name)
	glob.intern[name] = &aa

	return a
}

func (ghi *GhImport) ImportKinds(kmap []PatRep) bool {

	gh := ghi.gh
	glob := gh.glob

	gh_imp := ghi.gh_imp

	klen := len(gh_imp.kinds)

	kvec := make([]*Kind, klen)

	km := make(map[*Kind]*Kind, klen)
	kminv := make(map[*Kind]*Kind, klen)

	jx := 0

	for kname, k := range gh_imp.kinds {

		kvec[jx] = k
		jx++

		knameLocal := glob.MapIt(kmap, string(*kname))
		if knameLocal == nil {
			errMsg("Kind '%s' imported from %s is unmapped\n", kname, gh_imp.fullpath)
			return false
		}
		kLocal := gh.kinds[knameLocal]
		if kLocal == nil {
			errMsg("Kind '%s' imported from %s is mapped to nonexistent kind '%s'\n",
				kname, gh_imp.fullpath, knameLocal)
			return false
		}
		km[k] = kLocal
		kremap := kminv[kLocal]
		if kremap != nil {
			// We allow two equivalent kinds to be mapped to the same kind
			if !k.IsEquivalentTo (kremap) {
				errMsg("Inequivalent kinds '%s' and '%s' from %s are both mapped to '%s'\n",
					kname, kremap.name, gh_imp.fullpath, knameLocal)
				return false
			}
		} else {
			kminv[kLocal] = k
		}
	}
	// Now check that k1 is a subkind of k2 in gh_imp.kinds if and only if
	// km[k1] is a subkind of km[k2]

	for ix := 1; ix < klen; ix++ {
		ki := kvec[ix]
		for jx := 0; jx < ix; jx++ {
			kj := kvec[jx]
			if (ki.isSubkindOf(kj) != km[ki].isSubkindOf(km[kj]) ||
			    kj.isSubkindOf(ki) != km[kj].isSubkindOf(km[ki])) {
				errMsg("Subkind relation is not invariant mapping kinds '%s' and '%s' to '%s' and '%s'\n",
					ki, kj, km[ki], km[kj])
				return false
			}
		}
	}

	ghi.kmap = km
	kminv = nil  // hint to gc
	return true
}

// Map each variable from the imported context to a variable of the same kind
// in the importing context. Verify that the mapping is injective.
//
// It is awkward to need to do this; we could get away without it except for
// human-interface issues about naming/displaying the varibles in imported
// assertions. [We could display an imported assertion using the variables
// from the imported module, however the variables might have different kinds
// and this could confuse the user.]
func (ghi *GhImport) ImportVars(vmap []PatRep) bool {

	gh := ghi.gh
	glob := gh.glob
	gh_imp := ghi.gh_imp

	vm := make(map[*Variable]*Variable)
	vminv := make(map[*Variable]*Variable)

	for vname, s := range gh_imp.syms {
		v := s.asVar()
		if v == nil { continue }

		vnameLocal := glob.MapIt(vmap, string(*vname))
		if vnameLocal == nil {
			errMsg("Variable %s imported from %s is unmapped\n", 
				vname, gh_imp.fullpath)
			return false
		}
		sLocal, found := gh.syms[vnameLocal]
		if !found {
			errMsg("Variable %s imported from %s is mapped to nonexistent Variable %s\n",
				vname, gh_imp.fullpath, vnameLocal)
			return false
		}
		vLocal := sLocal.asVar()
		if vLocal == nil {
			errMsg("Variable %s imported from %s is mapped to an assertion %s\n",
				vname, gh_imp.fullpath, vnameLocal)
			return false
		}
		if vminv[vLocal] != nil {
			errMsg("Variables %s and %s imported from %s are both mapped to %s\n",
				vname, vminv[vLocal].name, gh_imp.fullpath, vnameLocal)
			return false
		}
		if !vLocal.kind.IsEquivalentTo(ghi.kmap[v.kind]) {
			errMsg("Variable %s imported from %s is mapped to variable %s of the wrong kind\n", vname, gh_imp.fullpath, vnameLocal)
			return false
		}
		vm[v] = vLocal
		vminv[vLocal] = v
	}

	ghi.vmap = vm
	vminv = nil  // hint to gc

	return true
}

func (ghi *GhImport) ImportTerms(tmap []PatRep) bool {

	gh := ghi.gh
	glob := gh.glob
	gh_imp := ghi.gh_imp

	tm := make(map[*Term]*Term)
	tminv := make(map[*Term]*Term)

	for tname, t := range gh_imp.terms {

		tnameLocal := glob.MapIt(tmap, string(*tname))
		if tnameLocal == nil {
			// For now, we require that all terms in the imported
			// context be mapped, to avoid issues with imported
			// assertions referring to unmapped terms. May want to
			// relax this later.
			errMsg("Term %s imported from %s is unmapped\n", 
				tname, gh_imp.fullpath)
			return false
		}
		tLocal, found := gh.terms[tnameLocal]
		if !found {
			// 'Axiomatic' terms, i.e. undefined terms, must
			// be mapped to a term in the importing context.
			if t.expr == nil {

				errMsg("Term '%s' imported from %s is mapped to nonexistent term '%s'\n",
					tname, gh_imp.fullpath, tnameLocal)
				return false
			}
			// A term _defined_ in the imported context need
			// not exist yet in the importing context.
			// We import such defined terms with opaquified definienses, since
			// indirectly imported terms might otherwise look 'axiomatic'.
			// [Note that the 'expr' member of a defined term is not really used
			// after the defthm is proven, other than to mark the term as 
			// optional in imports. We might consider omitting it.]
			// Note that the 1-1 check below prevents such an added
			// term from being the target of a later-mapped 
			// axiomatic term.
			ak := make([]*Kind, len (t.argkinds))
			for i, k := range t.argkinds {
				ak[i] = ghi.kmap[k]
			}
			tLocal = &Term{ghi.kmap[t.kind], tnameLocal, ak, glob.opaque, 0}
			gh.terms[tnameLocal] = tLocal
			tm[t] = tLocal
			tminv[tLocal] = t
			continue
		}
		if tminv[tLocal] != nil {
			// We disallow non-injective mappings; terms of the
			// same signature in general do not have the same
			// semantics. Consider /\ and \/.  If we had a notion
			// of term equality, we might allow it in that case;
			// but we don not.
			errMsg("Terms '%s' and '%s' imported from %s are both mapped to '%s'\n", tname, tminv[tLocal].name, gh_imp.fullpath, tnameLocal)
			return false
		}
		// OK, now check that the mapped term has appropriate
		// result and argument kinds.
		if !tLocal.kind.IsEquivalentTo(ghi.kmap[t.kind]) {
			errMsg("Term '%s' imported from %s is mapped to term '%s', which has the wrong result kind\n", tname, gh_imp.fullpath, tnameLocal)
			return false
		}
		if len(tLocal.argkinds) != len(t.argkinds) {
			errMsg("Term '%s' imported from %s is mapped to term '%s', which has different arity\n", tname, gh_imp.fullpath, tnameLocal)
			return false
		}
		for ix, ak := range tLocal.argkinds {
			if ak.IsEquivalentTo(ghi.kmap[t.argkinds[ix]]) { continue }
			errMsg("Term '%s' imported from %s is mapped to term '%s', which has the wrong kind for argument %d\n", tname, gh_imp.fullpath, tnameLocal, ix)
			return false
		}
		tm[t] = tLocal
		tminv[tLocal] = t
	}

	// TODO - FIXME - Handle definition terms
	ghi.tmap = tm
	tminv = nil  // gc hint

	return true
}

func (ghi *GhImport) ImportAssertions(amap []PatRep) bool {

	gh := ghi.gh
	glob := gh.glob
	gh_imp := ghi.gh_imp

	for sname, s := range gh_imp.syms {
		stmt := s.asStmt()
		if stmt == nil { continue } // skip variables

		// On the first pass, only check axioms
		if !stmt.axiomatic { continue }

		snameLocal := glob.MapIt(amap, string(*sname))
		if snameLocal == nil {
			errMsg("Axiom %s imported from %s is unmapped\n", 
				sname, gh_imp.fullpath)
			return false
		}
		sLocal, found := gh.syms[snameLocal]
		if !found {
			errMsg("Axiom %s imported from %s is mapped to nonexistent symbol %s\n",
				sname, gh_imp.fullpath, snameLocal)
			return false
		}
		stmtLocal := sLocal.asStmt()
		if stmtLocal == nil {
			errMsg("Axiom %s imported from %s is mapped to a variable %s\n",
				sname, gh_imp.fullpath, snameLocal)
			return false
		}
		// Note, we allow non-injective mappings of axioms (or indeed
		// any assertion) since for assertions we care about the
		// assertion structure (which we check matches), not the
		// assertion name.

		if !ghi.assertionMatch(stmtLocal, stmt) { return false }
	}

	// Pass 2: handle non-axiomatic assertions.
	for sname, s := range gh_imp.syms {
		stmt := s.asStmt()
		if stmt == nil { continue } // skip variables

		// On the 2nd pass, only check non-axioms
		if stmt.axiomatic { continue }

		snameLocal := glob.MapIt(amap, string(*sname))

		// drop unmapped (non-axiomatic) assertions
		if snameLocal == nil { continue }

		sLocal, found := gh.syms[snameLocal]
		if !found {
			// Add the mapped assertion to gh
			nvars := len(stmt.vars)
			varsloc := make([]*Variable, nvars)
			for ix, v := range stmt.vars {
				varsloc[ix] = ghi.vmap[v]
			}
			nhyps := len(stmt.hyps)
			hypsloc := make([]Expression, nhyps)
			for ix, exp := range stmt.hyps {
				hypsloc[ix] = ghi.exprMap(exp)
			}
			nconcs := len(stmt.concs)
			concsloc := make([]Expression, nconcs)
			for ix, exp := range stmt.concs {
				concsloc[ix] = ghi.exprMap(exp)
			}
			sloc := &Statement{
				snameLocal,
				varsloc, 
				stmt.wild_vars,
				hypsloc,
				concsloc,
				stmt.dv_vars,  // can share
				stmt.dv_bits,  // can share
				false }
			gh.syms[snameLocal] = sloc
			continue
		}
		stmtLocal := sLocal.asStmt()
		if stmtLocal == nil {
			errMsg("Statement %s imported from %s is mapped to a variable %s\n",
				sname, gh_imp.fullpath, snameLocal)
			return false
		}
		// Note, we allow non-injective mappings of axioms (or indeed
		// any assertion) since for assertions we care about the
		// assertion structure (which we check matches), not the
		// assertion name.

		if !ghi.assertionMatch(stmtLocal, stmt) { return false }
	}
	return true
}

// e is an expression from the imported context ghi.gh_imp .
// Create a corresponding mapped expression for the importing context ghi.gh .
func (ghi *GhImport) exprMap(e Expression) Expression {
	v := e.asIVar()
	if v != nil {
		return &IVar{ghi.kmap[v.kind], v.index}
	}
	te := e.asTermExpr()
	nargs := len(te.args)
	args := make([]Expression, nargs)
	for ix, exp := range te.args {
		args[ix] = ghi.exprMap(exp)
	}
	return &TermExpr{ghi.tmap[te.term], args}
}

// Does the expression e from the imported context match the expression
// eloc in the importing context to which it is mapped?
func (ghi *GhImport) exprMatch(eloc Expression, e Expression) bool {
	v := e.asIVar()
	if v != nil {
		vloc := eloc.asIVar()
		return (vloc != nil && v.index == vloc.index)
	}
	te := e.asTermExpr()
	teloc := eloc.asTermExpr()
	if teloc == nil { return false }

	if teloc.term != ghi.tmap[te.term] { return false }

	for ix, exp := range te.args {
		if !ghi.exprMatch(teloc.args[ix], exp) { return false }
	}
	return true
}

func badDv (sloc *Statement, s *Statement) {
	errMsg("Imported statement '%s' mapped to assertion '%s' with non-matching distinct variables conditions\n", s.name, sloc.name)
}

func (ghi *GhImport) assertionMatch (sloc *Statement, s *Statement) bool {

	// Note that some of the hypotheses and conclusions may be just
	// index variables. We check that the number of variables used in
	// the hypotheses and conclusions is the same, and their kinds map
	// correctly, to avoid having to check anything but the variable
	// indices when comparing the hypotheses and conclusions.
	// We do not, however, require that the particular variable choices
	// be consistent with the global variable mapping determined in
	// ghi.vmap, so long as the kinds are OK.

	nvars := len(s.vars)
	if len(sloc.vars) != nvars {
		errMsg("Imported statement '%s' mapped to assertion '%s' with different number of variables\n", s.name, sloc.name)
		return false
	}
	for ix, v := range s.vars {
		if !sloc.vars[ix].kind.IsEquivalentTo(ghi.kmap[v.kind]) {
			errMsg("Imported statement '%s' mapped to assertion '%s' with nonmatching variable kinds\n", s.name, sloc.name)
			return false
		}
	}

	nhyps := len(s.hyps)
	nconcs := len(s.concs)
	if len(sloc.hyps) != nhyps {
		errMsg("Imported statement '%s' mapped to assertion '%s' with different number of hypotheses\n", s.name, sloc.name)
		return false
	}
	if len(sloc.concs) != nconcs {
		errMsg("Imported statement '%s' mapped to assertion '%s' with different number of conclusions\n", s.name, sloc.name)
		return false
	}
	for ix, exp := range s.hyps {
		if !ghi.exprMatch(sloc.hyps[ix], exp) {
			errMsg("Imported statement '%s' mapped to assertion '%s' with non-matching hypothesis %d\n", s.name, sloc.name, ix)
			return false
		}
	}
	for ix, exp := range s.concs {
		if !ghi.exprMatch(sloc.concs[ix], exp) {
			errMsg("Imported statement '%s' mapped to assertion '%s' with non-matching conclusion %d\n", s.name, sloc.name, ix)
			return false
		}
	}
	ndv := len(s.dv_vars)
	if len(sloc.dv_vars) != ndv {
		badDv(sloc, s)
		return false
	}
	// Note, the variables are listed in dv_vars in increasing order
	for ix := 0; ix < ndv ; ix++ {
		if sloc.dv_vars[ix] != s.dv_vars[ix] {
			badDv(sloc, s)
			return false
		}
	}
	// dv_bits lengths must match since dv_vars lengths match.
	ndvb := len(s.dv_bits)
	for ix := 0; ix < ndvb ; ix++ {
		if sloc.dv_bits[ix] != s.dv_bits[ix] {
			badDv(sloc, s)
			return false
		}
	}
	return true
}
	
// Handle a Ghoulbert command.  Return true if successful, false on failure
func (gh *Ghoulbert) Command(cmd *Atom, arg SyntaxItem) bool {

	glob := gh.glob

	// All of the commands currently expect *List argument.
	l := arg.asList()
	if cmd == &glob.cmds.thm || cmd == &glob.cmds.defthm {
		gh.pip.thm_name = nil
		gh.pip.vars = nil
		ret := gh.ThmCmd(l, cmd == &glob.cmds.defthm)
		if ret == 0 {
			// return true below
		} else if ret == 1 {
			if cmd == &glob.cmds.defthm {
				errMsg("Expected 'defthm (NAME KIND (DEFNAME ARGKIND ...) ((DVAR ...) ...) ({HYPNAME HYP} ...) (CONC ...) (STEP ...))' but found\n '%s'\n", arg)
			} else {
				errMsg("Expected 'thm (NAME ((DVAR ...) ...) ({HYPNAME HYP} ...) (CONC ...) (STEP ...))' but found\n '%s'\n", arg)
			}
			return false
		} else {
			errMsg("Proving theorem %s ...\n", gh.pip.thm_name)
			if gh.pip.vars != nil {
				gh.pip.Show()
			}
			return false
		}
	} else if cmd == &glob.cmds.stmt {
		if l == nil || l.length != 4 {
			goto stmt_syntax
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
		varmap := make(map[*Atom]*IVar)
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
			hyps, concs, nil, nil, true}
		if dvarl.head != nil {
			if !gh.DvarsAdd(stmt, varmap, dvarl) {
				return false
			}
		}
		gh.syms[sname] = stmt
		if gh.verbose != 0 {
			fmt.Printf("%s %s\n", cmd, sname)
		}

	} else if cmd == &glob.cmds.variable {
		if l == nil || l.length < 1 || l.head.car.asAtom() == nil {
			goto var_syntax
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
	} else if cmd == &glob.cmds.term {
		if l == nil || l.length != 2 {
			goto term_syntax
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

	} else if cmd == &glob.cmds.kind {
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
	} else if cmd == &glob.cmds.subkind {
		if l == nil || l.length != 2 {
			goto subkind_syntax
		}
		k1name := l.head.car.asAtom()
		k2name := l.head.cdr.car.asAtom()
		if k1name == nil || k2name == nil {
			goto subkind_syntax
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
	} else if cmd == &glob.cmds._import {
		// import (URL (KIND_MAP) (VAR_MAP) (TERM_MAP) (ASSERTION_FILTER_MAP))
		if l == nil || l.length != 5 {
			goto import_syntax
		}
		rem := l.head
		url := rem.car.asAtom()
		if url == nil {
			errMsg("URL must be a token.\n")
			goto import_syntax
		}

		rem = rem.cdr
		kmap := mapSyntax(rem.car, "KIND_MAP")
		if kmap == nil {
			goto import_syntax
		}

		rem = rem.cdr
		vmap := mapSyntax(rem.car, "VAR_MAP")
		if vmap == nil {
			goto import_syntax
		}

		rem = rem.cdr
		tmap := mapSyntax(rem.car, "TERM_MAP")
		if tmap == nil {
			goto import_syntax
		}

		rem = rem.cdr
		amap := mapSyntax(rem.car, "ASSERTION_FILTER_MAP")
		if amap == nil {
			goto import_syntax
		}

		// Get a Ghoulbert for the imported context url, possibly relative
		// to the path for gh...
		// Look up normalized url in a map to avoid reading the file
		// more than once. Check for recursion.

		gh_imp := glob.GhoulbertForUrl(gh.basedir, string(*url), gh.verbose, gh.pretty_print)

		ghi := &GhImport{gh: gh, gh_imp: gh_imp}

		return (ghi.ImportKinds(kmap) && ghi.ImportVars(vmap) &&
			ghi.ImportTerms(tmap) && ghi.ImportAssertions(amap))

	} else {
		errMsg("Unknown command '%s'\n", *cmd)
		return false
	}
	return true

subkind_syntax:
	errMsg("Expected 'subkind (KIND1 KIND2)' but found '%s'\n",
		arg.String())
	return false

var_syntax:
	errMsg("Expected 'var (KINDNAME VARNAME ...)', but found '%s'\n",
		arg.String())
	return false

term_syntax:
	errMsg("Expected 'term (RESULTKIND (TERMSYM ARGKIND ...))' but found '%s'\n", arg.String())
	return false

stmt_syntax:
	errMsg("Expected 'stmt (NAME ((DVAR ...) ...) (HYP ...) (CONC ...))' but found\n '%s'\n", arg.String())
	return false

import_syntax:
	errMsg("Expected 'import (URL (KIND_MAP) (VAR_MAP) (TERM_MAP) (ASSERTION_FILTER_MAP))' but found 'import %s'\n",
		arg.String())
	return false
}

// Read and verify the proof file represented by p into the new Ghoulbert
// context gh.
func (gh *Ghoulbert) ReadVerify(p Parser) {
	var item SyntaxItem
	var e SyntaxErr
	var atom *Atom

	for {
		item = GetItem(p, false)
		e = item.asError()
		if e != Syntax_OK {
			if e != Syntax_EOF {
				errMsg("At line %d, %s\n", p.Line(), e.String())
			}
			break
		}
		atom = item.asAtom()
		if atom == nil {
			errMsg("Expected command at line %d, but found\n'%s'\n",
				p.Line(), item.String())
			break
		}
		// Hmm, here we assume each command has a single argument
		// syntax item
		item = GetItem(p, false)
		e = item.asError()
		if e != Syntax_OK {
			if e == Syntax_EOF {
				errMsg("Expected command argument, found EOF at line %d\n",
					p.Line())
			} else {
				errMsg("At line %d, %s\n", p.Line(), e.String())
			}
			break
		}
		// At this point we know that item is an *Atom or a *List
		if !gh.Command(atom, item) {
			errMsg("... at line %d\n", p.Line())
			break
		}
		/*
		   if atom != &gh.glob.cmds.thm {
		       fmt.Printf("%s %s\n", *atom, item.String())
		   }
		*/
	}
}

func use(gh *Ghoulbert) {
	return
}

func main() {
	var fname string

	var verbose uint

	flag.UintVar(&verbose, "v", 0, "Verbosity level.")

	var pretty bool // pretty-print proof stack (etc.)

	flag.BoolVar(&pretty, "p", false, "Pretty-print proof stack")

	flag.Parse()

	glob := newGhoulbertGlobal()

	if flag.NArg() == 0 {
		fname = ""
	} else {
		fname = flag.Arg(0)
	}
	gh := glob.GhoulbertForUrl(".", fname, verbose, pretty)
	use(gh)
}
