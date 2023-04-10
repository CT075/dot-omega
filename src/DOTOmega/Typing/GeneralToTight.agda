open import Level renaming (zero to lzero; suc to lsuc) hiding (Lift)
open import Relation.Binary using (DecSetoid)

module DOTOmega.Typing.GeneralToTight {ℓ}
    (TypeL : DecSetoid lzero ℓ)
    (TermL : DecSetoid lzero ℓ)
  where

open import Data.List

open import Data.Context

open import DOTOmega.Syntax TypeL TermL
open import DOTOmega.Typing TypeL TermL
open import DOTOmega.Typing.Properties TypeL TermL
open import DOTOmega.Typing.Tight TypeL TermL

postulate
  -- proof:
  -- narrow x to get Γ & x ~ S(B:J) ⊢ A ∈ K
  -- S[ B ∈ J ] is inert, so use general-tight to get Γ & x ~ S(B:J) ⊢ A ∈ K
  st-β-premise : ∀ {Γ A B J K x} →
    Γ inert-ctx →
    Γ ⊢#ty B ∈ J →
    Γ & x ~ Kd J ⊢ty openType x A ∈ K →
    Γ & x ~ Kd (S[ B ∈ J ]) ⊢#ty openType x A ∈ K

  -- This is clearly true, but at the moment, [Γ & x ~ T] is defined as a
  -- function performing some computation (as opposed to a constructor),
  -- which Agda can have trouble with unifying.
  unwrap-inert-ctx : ∀ {Γ x fact} → (Γ & x ~ fact) inert-ctx → Γ inert-ctx

mutual
  ctx-ctx# : ∀ {Γ} → Γ inert-ctx → Γ ctx → Γ ctx-#
  ctx-ctx# Γx-inert c-empty = c-empty-#
  ctx-ctx# Γx-inert (c-cons-ty Γctx Γ⊢τ∈K) =
    let Γinert = unwrap-inert-ctx Γx-inert
     in
    c-cons-ty-#
      (ctx-ctx# Γinert Γctx)
      (⊢→⊢#-ty Γinert Γ⊢τ∈K)
  ctx-ctx# Γx-inert (c-cons-kd Γctx Γ⊢K-kd) =
    let Γinert = unwrap-inert-ctx Γx-inert
     in
    c-cons-kd-#
      (ctx-ctx# Γinert Γctx)
      (⊢→⊢#-kd Γinert Γ⊢K-kd)

  ⊢→⊢#-tm : ∀ {Γ e τ} → Γ inert-ctx → Γ ⊢tm e ∈ τ → Γ ⊢#tm e ∈ τ
  ⊢→⊢#-tm Γinert (ty-var Γ[x]⊢>τ) = ty-var-# Γ[x]⊢>τ
  ⊢→⊢#-tm Γinert (ty-ℿ-intro Γ⊢e∈τ) = ty-ℿ-intro-# Γ⊢e∈τ
  ⊢→⊢#-tm Γinert (ty-ℿ-elim Γ⊢f∈τ₁⇒τ₂ Γ⊢x∈τ₁) =
    ty-ℿ-elim-#
      (⊢→⊢#-tm Γinert Γ⊢f∈τ₁⇒τ₂)
      (⊢→⊢#-tm Γinert Γ⊢x∈τ₁)
  ⊢→⊢#-tm Γinert (ty-new-intro Γ⊢defs∈τ) = ty-new-intro-# Γ⊢defs∈τ
  ⊢→⊢#-tm Γinert (ty-new-elim Γ⊢x∈[val]) =
    ty-new-elim-# (⊢→⊢#-tm Γinert Γ⊢x∈[val])
  ⊢→⊢#-tm Γinert (ty-let Γ⊢e₁∈τ Γ⊢e₂∈ρ) =
    ty-let-# (⊢→⊢#-tm Γinert Γ⊢e₁∈τ) Γ⊢e₂∈ρ
  ⊢→⊢#-tm Γinert (ty-rec-intro Γ⊢x∈τ) = ty-rec-intro-# (⊢→⊢#-tm Γinert Γ⊢x∈τ)
  ⊢→⊢#-tm Γinert (ty-rec-elim Γ⊢x∈μτ) = ty-rec-elim-# (⊢→⊢#-tm Γinert Γ⊢x∈μτ)
  ⊢→⊢#-tm Γinert (ty-and-intro Γ⊢x∈τ₁ Γ⊢x∈τ₂) =
    ty-and-intro-#
      (⊢→⊢#-tm Γinert Γ⊢x∈τ₁)
      (⊢→⊢#-tm Γinert Γ⊢x∈τ₂)
  ⊢→⊢#-tm Γinert (ty-sub Γ⊢e∈τ₁ Γ⊢τ₁≤τ₂) =
    ty-sub-#
      (⊢→⊢#-tm Γinert Γ⊢e∈τ₁)
      (⊢→⊢#-st Γinert Γ⊢τ₁≤τ₂)

  ⊢→⊢#-st : ∀ {Γ S U k} → Γ inert-ctx → Γ ⊢ty S ≤ U ∈ k → Γ ⊢#ty S ≤ U ∈ k
  ⊢→⊢#-st Γinert (st-refl Γ⊢A∈K) = st-refl-# (⊢→⊢#-ty Γinert Γ⊢A∈K)
  ⊢→⊢#-st Γinert (st-trans Γ⊢S≤T Γ⊢T≤U) =
    st-trans-#
      (⊢→⊢#-st Γinert Γ⊢S≤T)
      (⊢→⊢#-st Γinert Γ⊢T≤U)
  ⊢→⊢#-st Γinert (st-top Γ⊢A∈S∙∙U) = st-top-# (⊢→⊢#-ty Γinert Γ⊢A∈S∙∙U)
  ⊢→⊢#-st Γinert (st-bot Γ⊢A∈S∙∙U) = st-bot-# (⊢→⊢#-ty Γinert Γ⊢A∈S∙∙U)
  ⊢→⊢#-st Γinert (st-and-l₁ Γ⊢τ₁∧τ₂∈K) = st-and-l₁-# (⊢→⊢#-ty Γinert Γ⊢τ₁∧τ₂∈K)
  ⊢→⊢#-st Γinert (st-and-l₂ Γ⊢τ₁∧τ₂∈K) = st-and-l₂-# (⊢→⊢#-ty Γinert Γ⊢τ₁∧τ₂∈K)
  ⊢→⊢#-st Γinert (st-and₂ Γ⊢ρ≤τ₁∈K Γ⊢ρ≤τ₂∈K) =
    st-and₂-#
      (⊢→⊢#-st Γinert Γ⊢ρ≤τ₁∈K)
      (⊢→⊢#-st Γinert Γ⊢ρ≤τ₂∈K)
  ⊢→⊢#-st Γinert (st-field Γ⊢τ₁≤τ₂∈K) = st-field-# (⊢→⊢#-st Γinert Γ⊢τ₁≤τ₂∈K)
  ⊢→⊢#-st Γinert (st-typ Γ⊢J≤K) = st-typ-# (⊢→⊢#-sk Γinert Γ⊢J≤K)
  ⊢→⊢#-st Γinert (st-β₁ Γ⊢A∈K Γ⊢B∈J) =
    let Γ⊢#B∈J = ⊢→⊢#-ty Γinert Γ⊢B∈J
     in
    st-β₁-#
      Γ⊢#B∈J
      (st-β-premise Γinert Γ⊢#B∈J Γ⊢A∈K)
  ⊢→⊢#-st Γinert (st-β₂ Γ⊢A∈K Γ⊢B∈J) =
    let Γ⊢#B∈J = ⊢→⊢#-ty Γinert Γ⊢B∈J
     in
    st-β₂-#
      Γ⊢#B∈J
      (st-β-premise Γinert Γ⊢#B∈J Γ⊢A∈K)
  ⊢→⊢#-st Γinert (st-app Γ⊢A₁≤A₂ (st-antisym Γ⊢B₁≤B₂ Γ⊢B₂≤B₁)) =
    st-app-#
      (⊢→⊢#-st Γinert Γ⊢A₁≤A₂)
      (st-antisym-#
        (⊢→⊢#-st Γinert Γ⊢B₁≤B₂)
        (⊢→⊢#-st Γinert Γ⊢B₂≤B₁))
  ⊢→⊢#-st Γinert (st-bnd₁ Γ⊢A∈S∙∙U) = st-bnd₁-# (⊢→⊢#-ty Γinert Γ⊢A∈S∙∙U)
  ⊢→⊢#-st Γinert (st-bnd₂ Γ⊢A∈S∙∙U) = st-bnd₂-# (⊢→⊢#-ty Γinert Γ⊢A∈S∙∙U)

  ⊢→⊢#-ty : ∀ {Γ τ k} → Γ inert-ctx → Γ ⊢ty τ ∈ k → Γ ⊢#ty τ ∈ k
  ⊢→⊢#-ty Γinert (k-var Γctx Γ[x]⊢>τ) = k-var-# (ctx-ctx# Γinert Γctx) Γ[x]⊢>τ
  ⊢→⊢#-ty Γinert k-top = k-top-#
  ⊢→⊢#-ty Γinert k-bot = k-bot-#
  ⊢→⊢#-ty Γinert (k-sing Γ⊢A∈S∙∙U) = k-sing-# (⊢→⊢#-ty Γinert Γ⊢A∈S∙∙U)
  ⊢→⊢#-ty Γinert (k-arr Γ⊢A∈✶ Γ⊢B∈✶) = k-arr-# (⊢→⊢#-ty Γinert Γ⊢A∈✶) Γ⊢B∈✶
  ⊢→⊢#-ty Γinert (k-abs Γ⊢J-kd Γ⊢A∈K) =
    k-abs-#
      (⊢→⊢#-kd Γinert Γ⊢J-kd)
      Γ⊢A∈K
  ⊢→⊢#-ty Γinert (k-app Γ⊢f∈ℿJK Γ⊢τ∈J) =
    k-app-#
      (⊢→⊢#-ty Γinert Γ⊢f∈ℿJK)
      (⊢→⊢#-ty Γinert Γ⊢τ∈J)
  ⊢→⊢#-ty Γinert (k-intersect Γ⊢τ₁∈S₁∙∙U₁ Γ⊢τ₂∈S₂∙∙U₂) =
    k-intersect-#
      (⊢→⊢#-ty Γinert Γ⊢τ₁∈S₁∙∙U₁)
      (⊢→⊢#-ty Γinert Γ⊢τ₂∈S₂∙∙U₂)
  ⊢→⊢#-ty Γinert (k-sub Γ⊢τ∈J Γ⊢J≤K) =
    k-sub-#
      (⊢→⊢#-ty Γinert Γ⊢τ∈J)
      (⊢→⊢#-sk Γinert Γ⊢J≤K)
  ⊢→⊢#-ty Γinert (k-field Γ⊢τ∈A∙∙B) = k-field-# (⊢→⊢#-ty Γinert Γ⊢τ∈A∙∙B)
  ⊢→⊢#-ty Γinert (k-typ Γ⊢K-kd) = k-typ-# (⊢→⊢#-kd Γinert Γ⊢K-kd)
  ⊢→⊢#-ty Γinert (k-sel Γ⊢x∈[typA∶k]) = {! !}

  ⊢→⊢#-sk : ∀ {Γ J K} → Γ inert-ctx → Γ ⊢kd J ≤ K → Γ ⊢#kd J ≤ K
  ⊢→⊢#-sk Γinert (sk-intv Γ⊢S₂≤S₁ Γ⊢U₁≤U₂) =
    sk-intv-#
      (⊢→⊢#-st Γinert Γ⊢S₂≤S₁)
      (⊢→⊢#-st Γinert Γ⊢U₁≤U₂)
  ⊢→⊢#-sk Γinert (sk-darr Γ⊢ℿJ₁K₁-kd Γ⊢J₂≤J₁ Γ⊢K₁≤K₂) =
    sk-darr-#
      (⊢→⊢#-kd Γinert Γ⊢ℿJ₁K₁-kd)
      (⊢→⊢#-sk Γinert Γ⊢J₂≤J₁)
      Γ⊢K₁≤K₂

  ⊢→⊢#-kd : ∀ {Γ k} → Γ inert-ctx → Γ ⊢ k kd → Γ ⊢# k kd
  ⊢→⊢#-kd Γinert (wf-intv Γ⊢S∈✶ Γ⊢U∈✶) =
    wf-intv-#
      (⊢→⊢#-ty Γinert Γ⊢S∈✶)
      (⊢→⊢#-ty Γinert Γ⊢U∈✶)
  ⊢→⊢#-kd Γinert (wf-darr Γ⊢J-kd Γ⊢K-kd) =
    wf-darr-# (⊢→⊢#-kd Γinert Γ⊢J-kd) Γ⊢K-kd

