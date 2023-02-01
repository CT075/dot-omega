open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary using (DecSetoid)

module DOT.Syntax.Context {ℓ}
    (TypeL : DecSetoid lzero ℓ)
    (TermL : DecSetoid lzero ℓ)
  where

open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero)
open import Data.String using (String; _==_)
open import Data.List using (List; []; _∷_; map)
open import Data.Bool using (if_then_else_)

open import DOT.Syntax.Base TypeL TermL

-- TODO: This should live in [Var]
record Name : Set where
  constructor N
  field
    name : String
    index : ℕ

bump : String → Name → Name
bump x (N y i) = if x == y then N y (suc i) else N y i

record Entry : Set where
  constructor E
  field
    name : Name
    -- Types in the context can contain free variables, but they should be
    -- fully opened.
    typ : Type zero

weaken : String → Entry → Entry
weaken x (E y τ) = E (bump x y) τ

Ctx = List Entry

empty : Ctx
empty = []

put : Ctx → String → Type zero → Ctx
put xs x τ = (E (N x zero) τ) ∷ map (weaken x) xs

