import Mathlib

inductive Term
| bvar : ℕ → Term
| fvar : ℕ → Term
| lam  : Term → Term
| app  : Term → Term → Term

/-- bound substitution of the ith index -/
def Term.open_rec (i : ℕ) (sub : Term) : Term → Term
| bvar i' => if i = i' then sub else bvar i'
| fvar x  => fvar x
| app l r => app (open_rec i sub l) (open_rec i sub r)
| lam M   => lam $ open_rec (i+1) sub M

notation:68 e "⟦" i " ↝ " sub "⟧"=> Term.open_rec i sub e

--/-- bound substitution of the closest binding -/
def Term.open' (e u):= Term.open_rec 0 u e

infixr:80 " ^ " => Term.open'

def Term.subst (x : ℕ) (sub : Term) : Term → Term
| bvar i  => bvar i
| fvar x' => if x = x' then sub else fvar x'
| app l r => app (subst x sub l) (subst x sub r)
| lam M   => lam $ subst x sub M

notation:67 e "[" x ":=" sub "]" => Term.subst x sub e

/-- free variables of a term -/
def Term.fv : Term → Finset ℕ
| bvar _ => {}
| fvar x => {x}
| lam e1 => e1.fv
| app l r => l.fv ∪ r.fv

/-- locally closed terms -/
inductive Term.LC : Term → Prop
| fvar (x)  : LC (fvar x)
| lam (L : Finset ℕ) (e : Term) : (∀ x, x ∉ L → LC (e ^ fvar x)) → LC (lam e)
| app {l r} : l.LC → r.LC → LC (app l r)

/-- bind a free variable of a Term, so that the transformation `T` → `λ . T` makes sense -/
def Term.close_rec (k x : ℕ) : Term → Term
| fvar x' => if x = x' then bvar k else fvar x'
| bvar i  => bvar i
| app l r => app (close_rec k x l) (close_rec k x r)
| lam t   => lam $ close_rec (k+1) x t

notation:68 e "⟦" k " ↜ " x "⟧"=> Term.close_rec k x e

--/-- bound substitution of the closest binding -/
def Term.close (e u):= Term.close_rec 0 u e

infixr:80 " ^* " => Term.close

-- the remainder of this file is for notation
-- adapted from https://lean-lang.org/blog/2024-3-21-quasiquotation-with-binders-a-lean-metaprogramming-example/

open Std (Format)
open Lean.Parser (maxPrec argPrec minPrec)

def Term.format (prec : Nat) : Term → Format
| bvar x => s!"~{x.repr}"
| fvar x => s!"@{x.repr}"
| app e1 e2 => fmtApp <| e1.format argPrec ++ .line ++ e2.format maxPrec
| lam body => Format.paren <| "λ ." ++ .nest 2 (.line ++ body.format minPrec)
  where
    fmtApp (elts : Format) : Format :=
      Repr.addAppParen (.group (.nest 2 elts)) prec

instance Term.instRepr : Repr Term where
  reprPrec tm _ := .group <| .nest 2 (tm.format minPrec)
