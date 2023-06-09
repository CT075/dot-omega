open import Level renaming (zero to lzero; suc to lsuc) hiding (Lift)
open import Relation.Binary using (DecSetoid)

module DOTOmega.Typing.Invertible
    (TypeL : DecSetoid lzero lzero)
    (TermL : DecSetoid lzero lzero)
  where

open import DOTOmega.Syntax TypeL TermL
open import DOTOmega.Typing TypeL TermL
open import DOTOmega.Typing.Tight TypeL TermL
open import DOTOmega.Typing.Precise TypeL TermL

open import Data.Var
open import Data.Context

infix 4 _⊢##var_∈_
infix 4 _⊢##val_∈_

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
  ty-fun-## : ∀{x y S T S' T' J K} →
    Γ ⊢##var x ∈ ℿ S T →
    Γ ⊢#ty S' ≤ S ∈ J →
    Γ & y ~ Ty S' ⊢ty openType y T ≤ openType y T' ∈ K →
    Γ ⊢##var x ∈ ℿ S' T'
  ty-intersect-## : ∀{x A B} →
    Γ ⊢##var x ∈ A →
    Γ ⊢##var x ∈ B →
    Γ ⊢##var x ∈ A ∧ B
  ty-sel-## : ∀{x y τ M A} →
    Γ ⊢##var x ∈ A →
    Γ ⊢!var y ∈ τ ⟫ [ typ M ∶ A ∙∙ A ] →
    Γ ⊢##var x ∈ y ∙ M
  ty-rec-i-## : ∀{x τ} →
    Γ ⊢##var x ∈ plugType x τ →
    Γ ⊢##var x ∈ μ τ
  ty-top-## : ∀{x τ} →
    Γ ⊢##var x ∈ τ →
    Γ ⊢##var x ∈ ⊤
  {- I don't think this will work
  ty-equiv-## : ∀{x S U} →
    Γ ⊢##var x ∈ S →
    Γ ⊢#ty S == U ∈ ✶ →
    Γ ⊢##var x ∈ U
  -}

data _⊢##val_∈_ (Γ : Ctx VarFact) : Val → Type → Set where
  val-ty-## : ∀{v τ} →
    Γ ⊢!val v ∈ τ →
    Γ ⊢##val v ∈ τ
  val-intersect-i-## : ∀{v A B} →
    Γ ⊢##val v ∈ A →
    Γ ⊢##val v ∈ B →
    Γ ⊢##val v ∈ A ∧ B
  val-sel-## : ∀{v x τ M A} →
    Γ ⊢##val v ∈ A →
    Γ ⊢!var x ∈ τ ⟫ [ typ M ∶ A ∙∙ A ] →
    Γ ⊢##val v ∈ x ∙ M
  val-fun-## : ∀{v y S T S' T' J K} →
    Γ ⊢##val v ∈ ℿ S T →
    Γ ⊢#ty S' ≤ S ∈ J →
    Γ & y ~ Ty S' ⊢ty openType y T ≤ openType y T' ∈ K →
    Γ ⊢##val v ∈ ℿ S' T'
  val-top-## : ∀{v τ} →
    Γ ⊢##val v ∈ τ →
    Γ ⊢##val v ∈ ⊤
  val-equiv-## : ∀{v S U} →
    Γ ⊢##val v ∈ S →
    Γ ⊢#ty S == U ∈ ✶ →
    Γ ⊢##val v ∈ U
