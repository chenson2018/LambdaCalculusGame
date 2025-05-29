import Game.Metadata
import Game.LocallyNameless.Term

World "TermWorld"
Level 1

Title "Substitution"

Introduction "
A key idea of the lambda calculus is *substitution*. Intuitively, it is the
simple idea that functions taking arguments. For instance, we might have a
function that adds together numbers:
$$(λ x \\, . \\, λ y \\, . \\, x + y)$$

When expect that when we *apply* some arguments, that we should consistently
replace variable names to in some sense evaluate the function. This turns out to
be somewhat subtle. For instance, if we define variables in an abstraction as
strings, the terms $(λ x \\, .  \\, x)$ and $(λ y \\, .  \\, y)$ become
*syntactically* distinct, despite both representing what looks like an identity
function.

In this game we choose the *locally nameless* representation, which is in fact
what Lean itself uses. This method syntactically distinguishes between the
*free* and *bound* variables of a term.

Bound variables use *de Bruijn indices*, which refers to a
bound variable by a natural number that indicates how far away its binding is.
The example of addition above now becomes $(λ \\, . \\, λ \\, . \\, 1 + 0)$, while
both of the identity terms above become $(λ \\, . \\, 0)$.

In the locally nameless representation, substitution means substitution of free
variables, which now has no concern of overlap with bound variables. As an
example, let's try proving that $(λ \\, . \\, X)[X := Y] = (λ \\, . \\, Y)$.
"

open Term in
Statement (X Y : ℕ) : (lam (fvar X))[X := fvar Y] = lam (fvar Y) := by
  Hint "You can use either `unfold` or `simp` with `Term.subst`."
  Branch
    simp [subst]
  unfold subst
  unfold subst
  have h : X = X := by rfl
  simp [h]

Conclusion "Next, we'll see what the equivalent of substitution is for bound
variables"

/- Use these commands to add items to the game's inventory. -/

NewTactic rfl unfold simp «have»
-- NewTheorem Nat.add_comm Nat.add_assoc

/--
```
inductive Term
| bvar : ℕ → Term
| fvar : ℕ → Term
| lam  : Term → Term
| app  : Term → Term → Term
```

`Term` is a lambda calculus term, using the locally nameless representation.
-/
DefinitionDoc Term as "Term"

/--
```
def Term.subst (x : ℕ) (sub : Term) : Term → Term
| bvar i  => bvar i
| fvar x' => if x = x' then sub else fvar x'
| app l r => app (subst x sub l) (subst x sub r)
| lam M   => lam $ subst x sub M
```

Replacement of a free variable by a term.
-/
DefinitionDoc Term.subst as "subst"

-- TODO: Nat vs ℕ
NewDefinition Nat Term Term.subst
