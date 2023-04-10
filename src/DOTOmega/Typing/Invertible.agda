open import Level renaming (zero to lzero; suc to lsuc) hiding (Lift)
open import Relation.Binary using (DecSetoid)

module DOTOmega.Typing.Invertible {ℓ}
    (TypeL : DecSetoid lzero ℓ)
    (TermL : DecSetoid lzero ℓ)
  where

open import DOTOmega.Syntax TypeL TermL
open import DOTOmega.Typing TypeL TermL
open import DOTOmega.Typing.Tight TypeL TermL
open import DOTOmega.Typing.Precise TypeL TermL

open import Data.Var
open import Data.Context

infix 4 _⊢##var_∈_

data _⊢##var_∈_ (Γ : Ctx VarFact) : Var → Type → Set where
  ty-precise-## : ∀{x τ ρ} →
    Γ ⊢!var x ∈ τ ⟫ ρ →
    Γ ⊢##var x ∈ ρ
  ty-val-## : ∀{x ℓ τ ρ ✶} →
    Γ ⊢##var x ∈ [ val ℓ ∶ τ ] →
    Γ ⊢#ty τ ≤ ρ ∈ ✶ →
    Γ ⊢##var x ∈ [ val ℓ ∶ ρ ]
  ty-type-## : ∀{x M J K} →
    Γ ⊢##var x ∈ [ typ M ∶ J ] →
    Γ ⊢#kd J ≤ K →
    Γ ⊢##var x ∈ [ typ M ∶ K ]

