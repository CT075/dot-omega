open import Level renaming (zero to lzero; suc to lsuc) hiding (Lift)
open import Relation.Binary using (DecSetoid)

module DOTOmega.Typing.Precise.Properties
    (TypeL : DecSetoid lzero lzero)
    (TermL : DecSetoid lzero lzero)
  where

open import Data.List using ([] ; _∷_)
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding (J)

open import Data.Context

open import DOTOmega.Syntax TypeL TermL
open import DOTOmega.Typing TypeL TermL
open import DOTOmega.Typing.Tight TypeL TermL
open import DOTOmega.Typing.Tight.Properties TypeL TermL
open import DOTOmega.Typing.Precise TypeL TermL

record IsSingleton (Γ : Context) (K : Kind) : Set where
  constructor S
  field
    τ : Type
    J : Kind
    Γ⊢#τ∈J : Γ ⊢#ty τ ∈ J
    eq : K ≡ S[ τ ∈ J ]

postulate
  inert-lookup-ty : ∀ {Γ x τ} →
    Γ inert-ctx →
    Γ [ x ]⊢> Ty τ →
    τ inert-ty

precise-inert-τ : ∀ {Γ x τ ρ} →
  Γ inert-ctx →
  Γ ⊢!var x ∈ τ ⟫ ρ →
  τ inert-ty
precise-inert-τ Γinert (var-! Γ[x]⊢>τ) = inert-lookup-ty Γinert Γ[x]⊢>τ
precise-inert-τ Γinert (rec-e-! Γ⊢!x∈τ⟫μρ eq) rewrite eq =
  precise-inert-τ Γinert Γ⊢!x∈τ⟫μρ
precise-inert-τ Γinert (rec-and-!₁ Γ⊢!x∈τ⟫S∧U) = precise-inert-τ Γinert Γ⊢!x∈τ⟫S∧U
precise-inert-τ Γinert (rec-and-!₂ Γ⊢!x∈τ⟫S∧U) = precise-inert-τ Γinert Γ⊢!x∈τ⟫S∧U

precise-fun-is-fun : ∀ {Γ x τ₁ τ₂ ρ} →
  Γ ⊢!var x ∈ ℿ τ₁ τ₂ ⟫ ρ →
  Σ[ ρ' ∈ Type × Type ](ρ ≡ ℿ (proj₁ ρ') (proj₂ ρ'))
precise-fun-is-fun {τ₁ = τ₁} {τ₂ = τ₂} (var-! Γ[x]⊢>ℿτ₁τ₂) = ((τ₁ , τ₂) , refl)
precise-fun-is-fun (rec-e-! Γ⊢!x∈ℿτ₁τ₂⟫ρ eq) rewrite eq
  with precise-fun-is-fun Γ⊢!x∈ℿτ₁τ₂⟫ρ
... | ()
precise-fun-is-fun (rec-and-!₁ Γ⊢!x∈ℿτ₁τ₂⟫ρ) with precise-fun-is-fun Γ⊢!x∈ℿτ₁τ₂⟫ρ
... | ()
precise-fun-is-fun (rec-and-!₂ Γ⊢!x∈ℿτ₁τ₂⟫ρ) with precise-fun-is-fun Γ⊢!x∈ℿτ₁τ₂⟫ρ
... | ()

precise-recd-is-μ : ∀ {Γ x τ D} →
  Γ inert-ctx →
  Γ ⊢!var x ∈ τ ⟫ [ D ] →
  Σ[ ρ ∈ Type ](τ ≡ μ ρ)
precise-recd-is-μ Γinert Γ⊢!x∈[D] with precise-inert-τ Γinert Γ⊢!x∈[D]
... | μ-inert {τ} _ = (τ , refl)
... | ℿ-inert with precise-fun-is-fun Γ⊢!x∈[D]
...   | ()

un-μ : ∀ {a b} → μ a ≡ μ b → a ≡ b
un-μ refl = refl

data RecordOrRecurse (ρ : Type) (τ : Type) : Set where
  Record : τ recd → RecordOrRecurse ρ τ
  Recurse : τ ≡ μ ρ → RecordOrRecurse ρ τ

precise-μ-is-recd : ∀ {Γ x τ ρ} →
  Γ inert-ctx →
  Γ ⊢!var x ∈ μ ρ ⟫ τ →
  RecordOrRecurse ρ τ
precise-μ-is-recd Γinert (var-! Γ[x]⊢>μρ) = Recurse refl
precise-μ-is-recd Γinert (rec-e-! Γ⊢!x∈μρ⟫μρ' eq)
  with precise-μ-is-recd Γinert Γ⊢!x∈μρ⟫μρ'
... | Recurse eq' rewrite eq rewrite un-μ eq' =
  let μρ-inert = precise-inert-τ Γinert Γ⊢!x∈μρ⟫μρ'
      ρ-recd = unwrap μρ-inert
  in
    Record (plug-recd ρ-recd)
  where
    unwrap : ∀{ρ} → μ ρ inert-ty → ρ recd
    unwrap (μ-inert p) = p
-- this case is impossible by induction on the type [RecordLabels]
... | Record (ℓs , ())
precise-μ-is-recd Γinert (rec-and-!₁ Γ⊢!x∈μρ⟫S∧U)
  with precise-μ-is-recd Γinert Γ⊢!x∈μρ⟫S∧U
... | Record (_ , labels-join {ℓs₁ = Sℓs} S-is-recd U-is-recd disj) =
  Record (Sℓs , S-is-recd)
precise-μ-is-recd Γinert (rec-and-!₂ Γ⊢!x∈μρ⟫S∧U)
  with precise-μ-is-recd Γinert Γ⊢!x∈μρ⟫S∧U
... | Record (_ , labels-join {ℓs₂ = Uℓs} S-is-recd U-is-recd disj) =
  Record (Uℓs , U-is-recd)

precise-recd-kind-is-singleton : ∀ {Γ x τ M K} →
  Γ inert-ctx →
  Γ ⊢!var x ∈ τ ⟫ [ typ M ∶ K ] →
  IsSingleton Γ K
precise-recd-kind-is-singleton Γinert Γ⊢!x∈τ⟫[M∶K]
  with precise-recd-is-μ Γinert Γ⊢!x∈τ⟫[M∶K]
... | (ρ , eq) rewrite eq = {! !}
