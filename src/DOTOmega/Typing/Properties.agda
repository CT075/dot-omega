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
open import Data.Context

open import DOTOmega.Syntax TypeL TermL
open import DOTOmega.Typing TypeL TermL

mutual
  narrowing-sk-tm : ∀ {Γ e x τ J K} →
    Γ ⊢tm e ∈ τ →
    (pf : Γ [ x ]⊢> Kd K) →
    Γ ⊢kd J ≤ K →
    replace Γ x (Kd J) pf ⊢tm e ∈ τ
  narrowing-sk-tm (ty-ℿ-intro e∈ρ) pf J≤K = {!!}
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
  narrowing-sk-tm {Γ} {`(Free (N y i))} (ty-var {N x i'} Γ[x]⊢>τ) pf J≤K = {!!}
