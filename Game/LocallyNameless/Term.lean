
inductive Term (atom : Type)
| bvar : ℕ → Term atom
| fvar : atom → Term atom
| lam  : Term atom → Term atom
| app  : Term atom → Term atom → Term atom


