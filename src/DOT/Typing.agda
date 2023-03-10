open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary using (DecSetoid)

module DOT.Typing {ℓ}
    (TypeL : DecSetoid lzero ℓ)
    (TermL : DecSetoid lzero ℓ)
  where

open import Data.Var

open import DOT.Syntax TypeL TermL

infix 4 _⊢_∈_

data _⊢_∈_ : Ctx → Term → Type → Set where
  ty-var : ∀{Γ name τ} → Γ [ name ]⊢> τ → Γ ⊢ `(Free name) ∈ τ
  --ty-forall-intro : ∀{Γ x τ U e} → Γ ⊢ V(ƛ τ e) ∈ ℿ τ U
