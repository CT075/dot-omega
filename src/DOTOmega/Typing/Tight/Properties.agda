open import Level renaming (zero to lzero; suc to lsuc) hiding (Lift)
open import Relation.Binary using (DecSetoid)

module DOTOmega.Typing.Tight.Properties {ℓ}
    (TypeL : DecSetoid lzero ℓ)
    (TermL : DecSetoid lzero ℓ)
  where

open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality

open import DOTOmega.Syntax TypeL TermL
open import DOTOmega.Typing TypeL TermL
open import DOTOmega.Typing.Tight TypeL TermL
open import DOTOmega.Typing.Precise TypeL TermL

open import Data.Context

infix 4 _inert-kd _inert-ty _inert-ctx _recd

data RecordLabels : Type → List TypeLabel → Set where

_recd : Type → Set
τ recd = Σ[ ℓs ∈ List TypeLabel ] (RecordLabels τ ℓs)

data _inert-kd : Kind → Set where
  intv-inert : ∀ {A} → A ∙∙ A inert-kd
  pi-inert : ∀ {J K} → K inert-kd → ℿ J K inert-kd

data _inert-ty : Type → Set where
  pi-inert : ∀ {τ₁ τ₂} → ℿ τ₁ τ₂ inert-ty
  μ-inert : ∀ {τ} →
    τ recd →
    μ τ inert-ty

data _inert-ctx : Context → Set where
  empty-inert : [] inert-ctx
  cons-inert-ty : ∀ {Γ x τ} → Γ inert-ctx → τ inert-ty → Γ & x ~ Ty τ inert-ctx
  cons-inert-kd : ∀ {Γ x k} → Γ inert-ctx → k inert-kd → Γ & x ~ Kd k inert-ctx


postulate
  sing-sub : ∀{Γ τ k} → Γ ⊢ty τ ∈ k → Γ ⊢kd S[ τ ∈ k ] ≤ k

  sing-sub-# : ∀{Γ τ k} → Γ ⊢#ty τ ∈ k → Γ ⊢#kd S[ τ ∈ k ] ≤ k

  sing-inert : ∀ τ k → S[ τ ∈ k ] inert-kd

postulate
  dec-typ-inv : ∀ {Γ x τ M k} →
    Γ ⊢!var x ∈ τ ⟫ [ typ M ∶ k ] →
    Σ[ y ∈ Type × Kind ](k ≡ (S[ proj₁ y ∈ proj₂ y ]))
