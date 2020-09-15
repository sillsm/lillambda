//go 1.10.4

package main

import (
	"fmt"
	"reflect"
)

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
// Specifically alpha and beta reduction.
// beta reduction is performing a recursive reduction
// on Apply{Bind, ?...}.
//
// Alpha reduction is renaming bound variables
// so that running apply won't cause collisions.
// We get around it by applying a Scope{} struct
// to variable substitutions to, which feels cleaner.

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

func (b Bind) Reduce() Expression { return b }

func (s scope) Reduce() Expression { return s }

func (a Apply) Reduce() Expression {
	// the highest precedence goes to
	// apply{bind, ?}

	// Apply{scope{lambda}, x} ->
	// Apply{lambda, x}
	if v, ok := a.A1.(scope); ok {
		//fmt.Printf("Got here %v\n", String(Apply{v.E, a.A2}) )
		return Apply{v.E, a.A2}
	}

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

	var head, tail Expression
	// so we break the x? into the three cases
	switch v := rhs.(type) {
	case Var, Bind, scope:
		head = v
	case Apply:
		head = v.A1
		tail = v.A2
	}

	if head == nil {
		panic("unexpected")
	}
	// Peel off the leftmost lambda
	substitute := lhs.V
	// substitute the var throughout with
	// the innermost token, but don't go through
	// other lambdas so you don't need to
	// do alpha reduction

	// this logic is wrong, try a capture block
	// on substitution
	var sub func(Expression) Expression
	sub = func(e Expression) Expression {
		switch v := e.(type) {
		case Apply:
			return Apply{sub(v.A1), sub(v.A2)}
		case Var:
			if reflect.DeepEqual(v, substitute) {
				// where scope would go
				if _, ok := head.(scope); ok {
					return head
				}
				return scope{head}
			}
			return v
		case Bind:
			/*
			   if avoidCapture{
			     return v
			   }*/
			// we're still in the original lambda
			return Bind{v.V, sub(v.E)}
		}
		return e
	}

	// ret := sub(lhs.E)
	// Do we have more lambdas to pick through?
	_, ok := lhs.E.(Bind)

	// fmt.Printf("H|%v\nT|%v\n", head, tail)
	// reduced := sub(lhs.E)

	if tail != nil && ok {
		return Apply{sub(lhs.E), tail}
	}

	return sub(lhs.E)

	// fmt.Printf("A %v \nB %v\n", String(lhs),
	// String(rhs))
	// fmt.Printf("Tokens %v\n", tokens)
	return a
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
		return fmt.Sprintf("[%v|%v]",
			String(v.A1), String(v.A2))
	}
	return ""
}

/*
TRUE := λx.λy.x
FALSE := λx.λy.y

AND := λp.λq.p q p
OR := λp.λq.p p q
*/
func Compute(e Expression) Expression {

	halt := func(exp Expression) bool {
		// keep going as long as root node is apply
		v, ok := exp.(Apply)
		if !ok {
			return true
		}
		// and
		// left child is lambda or Apply or scope OR
		if _, ok := v.A1.(Bind); ok {
			return false
		}
		if _, ok := v.A1.(Apply); ok {
			return false
		}

		if _, ok := v.A1.(scope); ok {
			return false
		}

		// right child is Apply
		if _, ok := v.A2.(Apply); ok {
			return false
		}
		return true
	}

	fmt.Printf("\nStarting: %v\n", String(e))
	for i := 0; i < 20; i++ {
		if halt(e) {
			return e
		}
		e = e.Reduce()

		fmt.Printf("Step %v\n", String(e))
	}
	fmt.Println("Computation timeout at 20")
	return e
}

// λf.λx.f (f x) = 2

func main() {
	x, y := Var{"x"}, Var{"y"}
	p, q := Var{"p"}, Var{"q"}
	_, b, _ := Var{"a"}, Var{"b"}, Var{"c"}

	// lambda
	l := func(v Var, e ...Expression) Bind {
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
	a := func(e ...Expression) Apply {
		if len(e) < 2 {
			panic("trying to apply less than two args")
		}
		arg := Apply{e[0], e[1]}
		for i := 2; i < len(e); i++ {
			arg = Apply{arg, e[i]}
		}
		return arg
	}

	Id := Bind{x, x}
	True := Bind{x, Bind{y, x}}
	False := Bind{p, Bind{q, q}}
	And := Bind{p, Bind{q, Apply{p, Apply{q, p}}}}

	fmt.Printf("%v\n%v\n", String(True), String(And))

	Compute(Apply{scope{True}, False})
	//Compute(Apply{Apply{True, False}, True})
	Compute(Apply{True, Apply{Var{"m"}, Var{"n"}}})
	Compute(Apply{And, Apply{True, False}})
	//Compute(Scope{Apply{And, Apply{True, False}}})

	// bug it out
	Compute(Apply{Apply{True, False}, True})
	Compute(Apply{Apply{scope{True}, scope{False}},
		scope{True}})

	Compute(Apply{b, Apply{Id, x}})

	fmt.Printf("\nName Collision")
	// renaming issue
	// \y.\x.y) x
	Compute(Apply{l(y, l(x, y)), x})
	Compute(Apply{l(p, l(q, p, q, p)),
		Apply{True, False}})

	Compute(a(l(p, l(q, p, q, p)), True, False))
}
