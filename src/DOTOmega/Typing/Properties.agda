open import Level renaming (zero to lzero; suc to lsuc) hiding (Lift)
open import Relation.Binary using (DecSetoid)

module DOTOmega.Typing.Properties {ℓ}
    (TypeL : DecSetoid lzero ℓ)
    (TermL : DecSetoid lzero ℓ)
  where

open import Data.Bool using (true; false; if_then_else_)
open import Data.Nat using (zero; suc)
open import Data.List using ([]; map)
open import Data.Empty using (⊥-elim) renaming (⊥ to Void)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Nullary.Decidable using (Dec; isYes)
open import Relation.Binary.PropositionalEquality

open import Data.Var
open import Data.Var.Properties using (_≟_)
open import Data.Context
open import Data.Context.Properties

open import DOTOmega.Syntax TypeL TermL
open import DOTOmega.Typing TypeL TermL

postulate
  weakening-tm-sk : ∀ {Γ x τ J K} →
    Γ ⊢kd J ≤ K →
    Γ & x ~ Ty τ ⊢kd J ≤ K

  narrowing-sk-kd : ∀ {Γ τ x J₁ J₂ K} →
    Γ ⊢ty τ ∈ K →
    (pf : Γ [ x ]⊢> Kd J₁) →
    Γ ⊢kd J₁ ≤ J₂ →
    replace Γ x (Kd J₂) pf ⊢ty τ ∈ K

  narrowing-sk-tm : ∀ {Γ e x τ J K} →
    Γ ⊢tm e ∈ τ →
    (pf : Γ [ x ]⊢> Kd K) →
    Γ ⊢kd J ≤ K →
    replace Γ x (Kd J) pf ⊢tm e ∈ τ
{-
narrowing-sk-tm {Γ} {x = x} {J = J} (ty-ℿ-intro {y} {τ} {ρ} {e} e∈ρ) pf J≤K =
  ty-ℿ-intro narrow-e
  where
    narrow-e : replace Γ x (Kd J) pf & y ~ Ty τ ⊢tm openTerm y e ∈ openType y ρ
    narrow-e rewrite cong (λ t → t ⊢tm openTerm y e ∈ openType y ρ) (replace∘weaken pf) =
      {!
      narrowing-sk-tm e∈ρ (weaken Γ x y (Ty τ) pf) {! J≤K !}
      !}
narrowing-sk-tm (ty-ℿ-elim x∈τ₁⇒τ₂ z∈τ₁) pf J≤K =
  let narrow-x = narrowing-sk-tm x∈τ₁⇒τ₂ pf J≤K
      narrow-z = narrowing-sk-tm z∈τ₁ pf J≤K
   in
  ty-ℿ-elim narrow-x narrow-z
narrowing-sk-tm (ty-new-intro x) pf J≤K = {! !}
narrowing-sk-tm (ty-new-elim x∈[ℓ∶τ]) pf J≤K =
  let narrow-x = narrowing-sk-tm x∈[ℓ∶τ] pf J≤K
   in
  ty-new-elim narrow-x
narrowing-sk-tm (ty-let e∈τ x) pf J≤K = {! !}
narrowing-sk-tm (ty-rec-intro x∈τ[x]) pf J≤K = {! !}
narrowing-sk-tm (ty-rec-elim x∈μτ) pf J≤K = {! !}
narrowing-sk-tm (ty-and-intro x∈τ₁ x∈τ₂) pf J≤K =
  let narrow-x₁ = narrowing-sk-tm x∈τ₁ pf J≤K
      narrow-x₂ = narrowing-sk-tm x∈τ₂ pf J≤K
   in
  ty-and-intro narrow-x₁ narrow-x₂
narrowing-sk-tm (ty-sub e∈τ x) pf J≤K = {! !}
narrowing-sk-tm {Γ} {`(Free x)} {y} {τ} {J} {K} (ty-var Γ[x]⊢>τ) Γ[y]⊢>K J≤K
  with y ≟ x
... | no y≢x = ty-var (replace-spec-xy Γ y x (Kd J) (Ty τ) Γ[y]⊢>K Γ[x]⊢>τ y≢x)
... | yes y≡x rewrite y≡x =
  let K≡τ : Kd K ≡ Ty τ
      K≡τ = lookup-unique Γ[y]⊢>K Γ[x]⊢>τ

      K≢τ : Kd K ≢ Ty τ
      K≢τ = λ ()
   in
  ⊥-elim (K≢τ K≡τ)
-}
