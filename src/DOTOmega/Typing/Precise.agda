open import Level renaming (zero to lzero; suc to lsuc) hiding (Lift)
open import Relation.Binary using (DecSetoid)

module DOTOmega.Typing.Precise
    (TypeL : DecSetoid lzero lzero)
    (TermL : DecSetoid lzero lzero)
  where

open import Data.List using (map)
open import Relation.Binary.PropositionalEquality

open import DOTOmega.Syntax TypeL TermL
open import DOTOmega.Typing TypeL TermL

open import Data.Var
open import Data.Context

infix 4 _⊢!val_∈_
infix 4 _⊢!var_∈_⟫_

-- TODO: what if τ is a beta-redex?
data _⊢!var_∈_⟫_ (Γ : Ctx VarFact) : Var → Type → Type → Set where
  var-! : ∀{x τ} → Γ [ x ]⊢> Ty τ → Γ ⊢!var Free x ∈ τ ⟫ τ
  rec-e-! : ∀{x τ ρ xρ} →
    Γ ⊢!var Free x ∈ τ ⟫ μ ρ →
    xρ ≡ plugType (Free x) ρ →
    Γ ⊢!var Free x ∈ τ ⟫ xρ
  rec-and-!₁ : ∀{x τ S U} →
    Γ ⊢!var Free x ∈ τ ⟫ S ∧ U → Γ ⊢!var Free x ∈ τ ⟫ S
  rec-and-!₂ : ∀{x τ S U} →
    Γ ⊢!var Free x ∈ τ ⟫ S ∧ U → Γ ⊢!var Free x ∈ τ ⟫ U

data _⊢!val_∈_ (Γ : Ctx VarFact) : Val → Type → Set where
  fun-I-! : ∀{x τ t U} →
    Γ & x ~ Ty τ ⊢tm openTerm x t ∈ openType x U →
    Γ ⊢!val ƛ τ t ∈ ℿ τ U
  rec-I-! : ∀{x τ defs} →
    Γ & x ~ Ty (openType x τ) ⊢defns map (openDefn x) defs ∈ openType x τ →
    Γ ⊢!val new τ defs ∈ μ τ
