open import Level renaming (zero to lzero; suc to lsuc) hiding (Lift)
open import Relation.Binary using (DecSetoid)

module DOTOmega.TightTyping.Properties {ℓ}
    (TypeL : DecSetoid lzero ℓ)
    (TermL : DecSetoid lzero ℓ)
  where

open import Data.Context

open import DOTOmega.Syntax TypeL TermL
open import DOTOmega.Typing TypeL TermL
open import DOTOmega.TightTyping TypeL TermL

mutual
  narrowing-sk-tm : ∀ {Γ e x τ J K} →
    Γ & x ~ Kd K ⊢#tm e ∈ τ →
    Γ ⊢#kd J ≤ K →
    Γ & x ~ Kd J ⊢#tm e ∈ τ
  narrowing-sk-tm (ty-var-# Γ[x]⊢>τ) J≤K = {!!}
  narrowing-sk-tm (ty-ℿ-intro-# e∈ρ) J≤K = {! !}
  narrowing-sk-tm (ty-ℿ-elim-# x∈τ₁⇒τ₂ z∈τ₁) J≤K =
    let narrow-x = narrowing-sk-tm x∈τ₁⇒τ₂ J≤K
        narrow-z = narrowing-sk-tm z∈τ₁ J≤K
     in
    ty-ℿ-elim-# narrow-x narrow-z
  narrowing-sk-tm (ty-new-intro-# x) J≤K = {! !}
  narrowing-sk-tm (ty-new-elim-# x∈[ℓ∶τ]) J≤K =
    let narrow-x = narrowing-sk-tm x∈[ℓ∶τ] J≤K
     in
    ty-new-elim-# narrow-x
  narrowing-sk-tm (ty-let-# e∈τ x) J≤K = {! !}
  narrowing-sk-tm (ty-rec-intro-# x∈τ[x]) J≤K = {! !}
  narrowing-sk-tm (ty-rec-elim-# x∈μτ) J≤K = {! !}
  narrowing-sk-tm (ty-and-intro-# x∈τ₁ x∈τ₂) J≤K =
    let narrow-x₁ = narrowing-sk-tm x∈τ₁ J≤K
        narrow-x₂ = narrowing-sk-tm x∈τ₂ J≤K
     in
    ty-and-intro-# narrow-x₁ narrow-x₂
  narrowing-sk-tm (ty-sub-# e∈τ x) J≤K = {! !}

  narrowing-sk-st : ∀ {Γ x S U k J K} →
    Γ & x ~ Kd K ⊢#ty S ≤ U ∈ k →
    Γ ⊢#kd J ≤ K →
    Γ & x ~ Kd J ⊢#ty S ≤ U ∈ k
  narrowing-sk-st S≤U J≤K = {!!}
