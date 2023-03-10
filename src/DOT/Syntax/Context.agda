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

open import Data.Var using (Name; bump; N)

open import DOT.Syntax.Base TypeL TermL

record Entry : Set where
  constructor E
  field
    name : Name
    typ : Type

weaken : String → Entry → Entry
weaken x (E y τ) = E (bump x y) τ

Ctx = List Entry

empty : Ctx
empty = []

put : Ctx → String → Type → Ctx
put xs x τ = (E (N x zero) τ) ∷ map (weaken x) xs

infix 3 _[_]⊢>_

data _[_]⊢>_ : Ctx → Name → Type → Set where
  bind-hd : ∀{x i τ Γ} → ((E (N x i) τ) ∷ Γ) [ N x i ]⊢> τ
  bind-tl : ∀{ent name τ Γ} → Γ [ name ]⊢> τ → (ent ∷ Γ) [ name ]⊢> τ
