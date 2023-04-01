open import Level renaming (zero to lzero; suc to lsuc) hiding (Lift)
open import Relation.Binary using (DecSetoid)

module DOTOmega.Typing.Properties {ℓ}
    (TypeL : DecSetoid lzero ℓ)
    (TermL : DecSetoid lzero ℓ)
  where

open import Data.Bool using (true; false; if_then_else_)
open import Data.Nat using (zero; suc)
open import Data.List using ([]; map)
open import Data.String using (_≟_; _==_)
open import Data.Empty using (⊥-elim) renaming (⊥ to Void)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Nullary.Decidable using (Dec; isYes)
open import Relation.Binary.PropositionalEquality

open import Data.Var
open import Data.Context

open import DOTOmega.Syntax TypeL TermL
open import DOTOmega.Typing TypeL TermL

weakening-kd-tm : ∀ {Γ e x τ K} →
  Γ ⊢tm e ∈ τ →
  Γ & x ~ Kd K ⊢tm e ∈ shiftType x τ
weakening-kd-tm e∈τ = {!!}

mutual
  narrowing-sk-tm : ∀ {Γ e x τ J K} →
    Γ & x ~ Kd K ⊢tm e ∈ τ →
    Γ ⊢kd J ≤ K →
    Γ & x ~ Kd J ⊢tm e ∈ τ
  narrowing-sk-tm (ty-ℿ-intro e∈ρ) J≤K = {!!}
  narrowing-sk-tm (ty-ℿ-elim x∈τ₁⇒τ₂ z∈τ₁) J≤K =
    let narrow-x = narrowing-sk-tm x∈τ₁⇒τ₂ J≤K
        narrow-z = narrowing-sk-tm z∈τ₁ J≤K
     in
    ty-ℿ-elim narrow-x narrow-z
  narrowing-sk-tm (ty-new-intro x) J≤K = {! !}
  narrowing-sk-tm (ty-new-elim x∈[ℓ∶τ]) J≤K =
    let narrow-x = narrowing-sk-tm x∈[ℓ∶τ] J≤K
     in
    ty-new-elim narrow-x
  narrowing-sk-tm (ty-let e∈τ x) J≤K = {! !}
  narrowing-sk-tm (ty-rec-intro x∈τ[x]) J≤K = {! !}
  narrowing-sk-tm (ty-rec-elim x∈μτ) J≤K = {! !}
  narrowing-sk-tm (ty-and-intro x∈τ₁ x∈τ₂) J≤K =
    let narrow-x₁ = narrowing-sk-tm x∈τ₁ J≤K
        narrow-x₂ = narrowing-sk-tm x∈τ₂ J≤K
     in
    ty-and-intro narrow-x₁ narrow-x₂
  narrowing-sk-tm (ty-sub e∈τ x) J≤K = {! !}
  narrowing-sk-tm {Γ} {`(Free (N y i))} {x} {τ} {J} {K} (ty-var p) J≤K with i
  ... | suc _ = ty-var (hd-replace-suc Γ (Kd K) (Kd J) p)
  ... | zero with x ≟ y
  ...   | yes x≡y = ⊥-elim (p is-absurd)
            where
              _is-absurd : Kd K ≢ Ty τ
              _is-absurd ()
          -- XXX: This case took me 3 hours and is still messier than I'd like.
          -- I'm convinced there's a cleaner way to push the fact that [x ≟ y]
          -- is [no] into the type of [p], allowing it to normalize to
          -- [map (shiftEntry x) Γ [N y zero]⊢> Ty τ].
  ...   | no x≢y = ty-var (hd-replace-zero Γ (Kd K) (Kd J) (rewrite-if-false p) x≢y)
            where
              open ≡-Reasoning

              x==y≡false : (x == y) ≡ false
              x==y≡false with x ≟ y
              ... | yes x≡y = ⊥-elim (x≢y x≡y)
              ... | no _ = refl

              if-false : ∀ t₁ t₂ → (if x == y then t₁ else t₂) ≡ t₂
              if-false t₁ t₂ = cong (λ e → if e then t₁ else t₂) x==y≡false

              rewrite-if-false : ∀{t} →
                map (shiftEntry x) Γ [ N y zero ]⊢> Ty τ →
                if x == y then
                  t
                else
                  (map (shiftEntry x) Γ [ N y zero ]⊢> Ty τ)
              rewrite-if-false {t} p
                rewrite if-false t (map (shiftEntry x) Γ [ N y zero ]⊢> Ty τ)
                = p
