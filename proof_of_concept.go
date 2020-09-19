//go 1.10.4

package main

import (
	"fmt"
	"reflect"
)

const verbose = false

// lambda calculus
// expressions verified with
// https://crypto.stanford.edu/~blynn/lambda/

// An Expression is a thing which can reduce.
type Expression interface {
	Reduce() Expression
}

// lambda calculus is a binary expression
// tree with 3 node types: Var, Bind, and Apply
//
// Var is terminal; Bind and Apply can have children
//
// Computation is reducing the expression until you
// can't any longer.
//
// We found a technique to avoid the ugliness of
// alpha conversion or de bruijn numbering,
// by putting angle brackets around a
// substituted variable whenever
// in Apply{Bind{VAR, LHS}, RHS}
// Bound(LHS) intersect Free(RHS) is nonempty.

type Var struct {
	V string
}

type Bind struct {
	V Var
	E Expression
}

type Apply struct {
	A1, A2 Expression
}

// we use a scope sigil for
// substituted expressions so
// we don't have to worry about
// renaming (alpha conversion)
type scope struct {
	E Expression
}

// That's it. Now to reduction rules:
// they are trivial but for Apply, where we
// define alpha and beta reduction.

func (v Var) Reduce() Expression { return v }

// if you're a lambda at head, keep recursively
// going until you can find an apply,
// or you end the traversal
func (b Bind) Reduce() Expression {
	return Bind{b.V, b.E.Reduce()}
}

// if Bound(lhs) intersects Free(rhs)
// that's a collision that requires renaming
// (or scope struct on right side?)
func (s scope) Reduce() Expression { return s }

// bound returns the first string
// of lambda terms on LHS
func bound(e Expression) []Var {
	var ret []Var
	var f func(Expression)
	f = func(exp Expression) {
		switch v := exp.(type) {
		case Bind:
			ret = append(ret, v.V)
			f(v.E)
		case Var:
			// pass
		case scope:
			f(v.E)
		case Apply:
			f(v.A1)
			f(v.A2)
		}
	}
	f(e)
	return ret
}

func scopeCollissions(e Expression, b []Var) Expression {
	myBound := bound(e)
	var f func(Expression) Expression
	f = func(exp Expression) Expression {
		// If you're a var and you collide, scope
		// otherwise recurse.
		switch v := exp.(type) {
		case Var:
			for _, collision := range b {
				for _, term := range myBound {
					if reflect.DeepEqual(collision, term) {
						return v
					}
				}
				if reflect.DeepEqual(collision, v) {
					return scope{v}
				}
			}
			return v
		case Apply:
			return Apply{f(v.A1), f(v.A2)}
		case Bind:
			return Bind{v.V, f(v.E)}
		case scope:
			return v
		}
		panic("shouldn't get here")
	}
	return f(e)
}

func (a Apply) Reduce() Expression {
	// the highest precedence goes to
	// apply{bind, ?}

	// after trying that,
	// if either child is apply, try to recursively
	// eval until we get a bind
	if _, ok := a.A1.(Apply); ok {
		//fmt.Printf("Attempt reduction a1 %v\n",
		//String(a.A1))
		return Apply{a.A1.Reduce(), a.A2}
	}

	if _, ok := a.A2.(Apply); ok {
		if _, ok2 := a.A1.(Bind); !ok2 {
			return Apply{a.A1, a.A2.Reduce()}
		}
	}

	lhs, ok1 := a.A1.(Bind)
	if !ok1 {
		return a
	}
	rhs := a.A2
	// Now we're sure we have Apply{Bind, x?}
	// Tokenize rhs. Break up nodes through first
	// run of applies.

	// Peel off the leftmost lambda
	substitute := lhs.V
	// Put scope{} sigils around
	// free variables on RHS that are
	// bound on LHS
	rhs = scopeCollissions(rhs, bound(lhs.E))

	var sub func(Expression) Expression
	sub = func(e Expression) Expression {
		switch v := e.(type) {
		case Apply:
			return Apply{sub(v.A1), sub(v.A2)}
		case Var:
			if reflect.DeepEqual(v, substitute) {
				return rhs
			}
			return v
		case Bind:
			if reflect.DeepEqual(v.V, substitute) {
				return v
			}
			return Bind{v.V, sub(v.E)}
		}
		return e
	}
	return sub(lhs.E)
}

func String(e Expression) string {
	switch v := e.(type) {
	case scope:
		return fmt.Sprintf("<%v>", String(v.E))
	case Var:
		return v.V
	case Bind:
		return fmt.Sprintf("(λ%v.%v)",
			String(v.V), String(v.E))
	case Apply:
		return fmt.Sprintf("(%v %v)",
			String(v.A1), String(v.A2))
	}
	return ""
}

func Compute(e Expression) Expression {
	// keep going until no reduction was made
	last := e
	if verbose {
		fmt.Printf("\nStarting: %v\n", String(e))
	}
	for i := 0; i < 20; i++ {
		e = e.Reduce()
		if verbose {
			fmt.Printf("Step %v\n", String(e))
		}
		if reflect.DeepEqual(last, e) {
			return e
		}
		last = e

	}
	if verbose {
		fmt.Println("Computation timeout at 20")
	}
	// remove top level scopes as redundant
	if v, ok := e.(scope); ok {
		return v.E
	}
	return e
}

/*
 *  HELPER FUNCTIONS for prettier expressions
 */
func l(v Var, e ...Expression) Bind {
	if len(e) == 0 {
		panic("trying to make lambda expression with no body")
	}
	if len(e) == 1 {
		return Bind{v, e[0]}
	}
	arg := Apply{e[0], e[1]}
	for i := 2; i < len(e); i++ {
		arg = Apply{arg, e[i]}
	}

	return Bind{v, arg}
}

// apply
func a(e ...Expression) Apply {
	if len(e) < 2 {
		panic("trying to apply less than two args")
	}
	arg := Apply{e[0], e[1]}
	for i := 2; i < len(e); i++ {
		arg = Apply{arg, e[i]}
	}
	return arg
}

// scope wrap an expression
func s(e Expression) scope {
	return scope{e}
}

func main() {
	if test() {
		fmt.Printf("Tests passed successfully")
	}
}

// To be refactored to test file
func test() bool {
	// TODO: replace all tests with de bruijn indices

	x, y, f := Var{"x"}, Var{"y"}, Var{"f"}
	p, q := Var{"p"}, Var{"q"}
	A, B, C := Var{"a"}, Var{"b"}, Var{"c"}
	m, n := Var{"m"}, Var{"n"}

	Id := l(x, x)
	True := l(x, l(y, x))
	False := l(x, l(y, y))
	And := l(p, l(q, p, q, p))

	//mul  λm.λn.λf.m (n f)
	Mul := l(m, l(n, l(f, m, a(n, f))))
	Plus := l(p, l(q, l(f, l(x, p, f, a(q, f, x)))))

	// church numbers
	churchN := func(i int) Bind {
		body := Apply{Var{"f"}, x}
		if i < 0 {
			panic("No")
		}
		for i > 1 {
			body = Apply{Var{"f"}, body}
			i--
		}
		return l(Var{"f"}, l(x, body))
	}

	table := []struct {
		description string
		input       Expression
		output      Expression
	}{

		{"and true false = false",
			a(And, True, False),
			False,
		},
		{
			"2 + 2 = 4",
			a(Plus, churchN(2), churchN(2)),
			churchN(4),
		},
		{
			"3*5 = 15",
			a(Mul, churchN(3), churchN(5)),
			churchN(15),
		},
		{
			"(λp.λy.p y) (λx.λq.q x) q",
			a(l(p, l(y, p, y)), l(x, l(q, q, x)), q),
			l(q, q, s(q)),
		},
		{
			"(λx.λf.λx.x) m (Check that double binds parse correctly)",
			a(l(x, l(Var{"f"}, l(x, x))), Var{"m"}),
			l(Var{"f"}, l(x, x)),
		},
		{
			"(λf.λx.f (f x)) (λf.λx.f (f x)) (λx.x) (λx.x)",
			a(churchN(2), churchN(2), Id, Id),
			Id,
		},
		{
			"(λa.λb.λc.a a b c) (λx.c) (λx.c) (would require several alpha steps)",
			a(l(A, l(B, l(C, A, A, B, C))), l(x, C), l(x, C)),
			l(C, a(s(C), l(x, s(C))), C),
		},
	}
	pass := true
	for _, tt := range table {
		result := Compute(tt.input)
		if !reflect.DeepEqual(result, tt.output) {
			pass = false
			fmt.Printf("Failure: %v\n want %v\n got %v\n", tt.description,
				String(tt.output), String(result))
		}
	}
	return pass
}
