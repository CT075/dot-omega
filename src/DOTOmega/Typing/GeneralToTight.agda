open import Level using () renaming (zero to lzero; suc to lsuc)
open import Relation.Binary using (DecSetoid)

module DOTOmega.Typing.GeneralToTight {ℓ}
    (TypeL : DecSetoid lzero ℓ)
    (TermL : DecSetoid lzero ℓ)
  where

open import Data.Nat using (ℕ; suc; _⊔_; s≤s) renaming (_<_ to _<ℕ_)
open import Data.Nat.Properties using (≤-reflexive; m≤m⊔n; m≤n⊔m)
open import Data.Nat.Induction.Extensions
open import Data.Product
open import Data.List hiding ([_])
open import Relation.Binary.PropositionalEquality
open import Induction.WellFounded using (Acc; acc)

open import Data.Context
open import Data.Var

open import DOTOmega.Syntax TypeL TermL
open import DOTOmega.Typing TypeL TermL
open import DOTOmega.Typing.Properties TypeL TermL
open import DOTOmega.Typing.Tight TypeL TermL
open import DOTOmega.Typing.Tight.Properties TypeL TermL
open import DOTOmega.Typing.Precise TypeL TermL
open import DOTOmega.Typing.Invertible TypeL TermL
open import DOTOmega.Typing.Invertible.Properties TypeL TermL

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

record KSelPremise (Γ : Context) (x : Var) (M : TypeLabel) (k : Kind) : Set where
  constructor KS
  field
    τ : Type
    Γ⊢#τ∈k : Γ ⊢#ty τ ∈ k
    U : Type
    Γ⊢!x∈S[τ∶k] : Γ ⊢!var x ∈ U ⟫ [ typ M ∶ S[ τ ∈ k ] ]

k-sel-premise : ∀ {Γ x M k} →
  Γ inert-ctx →
  Γ ⊢#tm ` x ∈ [ typ M ∶ k ] →
  KSelPremise Γ x M k
k-sel-premise {Γ} {x} {M} {k} Γinert Γ⊢#x∈[M∶k] =
  k-sel-premise-## (⊢#→⊢##-var Γinert Γ⊢#x∈[M∶k])
  where
    -- TODO: this is the most important part of the proof
    postulate
      k-sel-premise-## : Γ ⊢##var x ∈ [ typ M ∶ k ] → KSelPremise Γ x M k
    {-
    k-sel-premise-## (ty-precise-## Γ⊢!x∈[M∶k]) = {! !}
    k-sel-premise-## (ty-type-## Γ⊢##x∈[M∶J] Γ⊢#J≤K) = {! !}
    -}

-- This extremely nasty well-founded induction is necessary to tell the
-- termination checker that narrowing the kinding judgment doesn't create
-- a taller derivation tree.

data Judgment : Context → Set → Set where
  IsCtx : ∀{Γ} → Γ ctx → Judgment Γ (Γ ctx-#)
  Typing : ∀{Γ e τ} → Γ ⊢tm e ∈ τ → Judgment Γ (Γ ⊢#tm e ∈ τ)
  Subtyping : ∀{Γ S U K} → Γ ⊢ty S ≤ U ∈ K → Judgment Γ (Γ ⊢#ty S ≤ U ∈ K)
  IsKd : ∀{Γ K} → Γ ⊢ K kd → Judgment Γ (Γ ⊢# K kd)
  Kinding : ∀{Γ τ K} → Γ ⊢ty τ ∈ K → Judgment Γ (Γ ⊢#ty τ ∈ K)
  Subkinding : ∀{Γ J K} → Γ ⊢kd J ≤ K → Judgment Γ (Γ ⊢#kd J ≤ K)

Judgment-height : ∀ {Γ Out} → Judgment Γ Out → ℕ
Judgment-height (IsCtx Γctx) = []ctx-h Γctx
Judgment-height (Typing Γ⊢e∈τ) = ⊢tm[]∈[]-h Γ⊢e∈τ
Judgment-height (Subtyping Γ⊢S≤U∈K) = ⊢ty[]≤[]∈[]-h Γ⊢S≤U∈K
Judgment-height (IsKd Γ⊢K-kd) = ⊢[]kd-h Γ⊢K-kd
Judgment-height (Kinding Γ⊢τ∈K) = ⊢ty[]∈[]-h Γ⊢τ∈K
Judgment-height (Subkinding Γ⊢J≤K) = ⊢kd[]≤[]-h Γ⊢J≤K

PackedJudgment : Set (lsuc lzero)
PackedJudgment = Σ[ p ∈ Context × Set ](Judgment (proj₁ p) (proj₂ p))

unpack : PackedJudgment → Set
unpack ((Γ , Out) , j) = Γ inert-ctx → Out

PackedJudgment-height : PackedJudgment → ℕ
PackedJudgment-height (_ , j) = Judgment-height j

_<_ : PackedJudgment → PackedJudgment → Set
j < j' = PackedJudgment-height j <ℕ PackedJudgment-height j'

<-wf : ∀ j → Acc _<_ j
<-wf = accMeasure PackedJudgment-height

⊢→⊢#-step : ∀ (packed@((Γ , Out) , j) : PackedJudgment) →
  Γ inert-ctx →
  Acc _<_ packed →
  Out

-- Context transformation
⊢→⊢#-step (_ , (IsCtx c-empty)) Γinert (acc rec) = c-empty-#
⊢→⊢#-step (_ , (IsCtx (c-cons-ty Γctx Γ⊢τ∈K))) Γx-inert (acc rec) =
  let Γinert = unwrap-inert-ctx Γx-inert
   in
  c-cons-ty-#
    (⊢→⊢#-step (_ , IsCtx Γctx) Γinert (rec _ (s≤s (m≤m⊔n _ _))))
    (⊢→⊢#-step (_ , Kinding Γ⊢τ∈K) Γinert (rec _ (s≤s (m≤n⊔m _ _))))
⊢→⊢#-step (_ , (IsCtx (c-cons-kd Γctx Γ⊢K-kd))) Γx-inert (acc rec) =
  let Γinert = unwrap-inert-ctx Γx-inert
   in
  c-cons-kd-#
    (⊢→⊢#-step (_ , IsCtx Γctx) Γinert (rec _ (s≤s (m≤m⊔n _ _))))
    (⊢→⊢#-step (_ , IsKd Γ⊢K-kd) Γinert (rec _ (s≤s (m≤n⊔m _ _))))

-- Type assignment
⊢→⊢#-step (_ , Typing (ty-var Γ[x]⊢>τ)) Γinert (acc rec) = ty-var-# Γ[x]⊢>τ
⊢→⊢#-step (_ , Typing (ty-ℿ-intro Γ⊢e∈τ)) Γinert (acc rec) = ty-ℿ-intro-# Γ⊢e∈τ
⊢→⊢#-step (_ , Typing (ty-ℿ-elim Γ⊢f∈τ₁⇒τ₂ Γ⊢x∈τ₁)) Γinert (acc rec) =
  ty-ℿ-elim-#
    (⊢→⊢#-step (_ , Typing Γ⊢f∈τ₁⇒τ₂) Γinert (rec _ (s≤s (m≤m⊔n _ _))))
    (⊢→⊢#-step (_ , Typing Γ⊢x∈τ₁) Γinert (rec _ (s≤s (m≤n⊔m _ _))))
⊢→⊢#-step (_ , Typing (ty-new-intro Γ⊢defs∈τ)) Γinert (acc rec) =
  ty-new-intro-# Γ⊢defs∈τ
⊢→⊢#-step (_ , Typing (ty-new-elim Γ⊢x∈[val])) Γinert (acc rec) =
  ty-new-elim-#
    (⊢→⊢#-step (_ , Typing Γ⊢x∈[val]) Γinert (rec _ (s≤s (≤-reflexive refl))))
⊢→⊢#-step (_ , Typing (ty-let Γ⊢e₁∈τ Γ⊢e₂∈ρ)) Γinert (acc rec) =
  ty-let-#
    (⊢→⊢#-step (_ , Typing Γ⊢e₁∈τ) Γinert (rec _ (s≤s (m≤m⊔n _ _)))) Γ⊢e₂∈ρ
⊢→⊢#-step (_ , Typing (ty-rec-intro Γ⊢x∈τ)) Γinert (acc rec) =
  ty-rec-intro-#
    (⊢→⊢#-step (_ , Typing Γ⊢x∈τ) Γinert (rec _ (s≤s (≤-reflexive refl))))
⊢→⊢#-step (_ , Typing (ty-rec-elim Γ⊢x∈μτ)) Γinert (acc rec) =
  ty-rec-elim-#
    (⊢→⊢#-step (_ , Typing Γ⊢x∈μτ) Γinert (rec _ (s≤s (≤-reflexive refl))))
⊢→⊢#-step (_ , Typing (ty-and-intro Γ⊢x∈τ₁ Γ⊢x∈τ₂)) Γinert (acc rec) =
    ty-and-intro-#
      (⊢→⊢#-step (_ , Typing Γ⊢x∈τ₁) Γinert (rec _ (s≤s (m≤m⊔n _ _))))
      (⊢→⊢#-step (_ , Typing Γ⊢x∈τ₂) Γinert (rec _ (s≤s (m≤n⊔m _ _))))
⊢→⊢#-step (_ , Typing (ty-sub Γ⊢e∈τ₁ Γ⊢τ₁≤τ₂)) Γinert (acc rec) =
    ty-sub-#
      (⊢→⊢#-step (_ , Typing Γ⊢e∈τ₁) Γinert (rec _ (s≤s (m≤m⊔n _ _))))
      (⊢→⊢#-step (_ , Subtyping Γ⊢τ₁≤τ₂) Γinert (rec _ (s≤s (m≤n⊔m _ _))))

-- Subtyping
⊢→⊢#-step (_ , Subtyping (st-refl Γ⊢A∈K)) Γinert (acc rec) =
  st-refl-# (⊢→⊢#-step (_ , Kinding Γ⊢A∈K) Γinert (rec _ (s≤s (≤-reflexive refl))))
⊢→⊢#-step (_ , Subtyping (st-trans Γ⊢A≤B Γ⊢B≤C)) Γinert (acc rec) =
  st-trans-#
    (⊢→⊢#-step (_ , Subtyping Γ⊢A≤B) Γinert (rec _ (s≤s (m≤m⊔n _ _))))
    (⊢→⊢#-step (_ , Subtyping Γ⊢B≤C) Γinert (rec _ (s≤s (m≤n⊔m _ _))))
⊢→⊢#-step (_ , Subtyping (st-top Γ⊢A∈S∙∙U)) Γinert (acc rec) =
  st-top-# (⊢→⊢#-step (_ , Kinding Γ⊢A∈S∙∙U) Γinert (rec _ (s≤s (≤-reflexive refl))))
⊢→⊢#-step (_ , Subtyping (st-bot Γ⊢A∈S∙∙U)) Γinert (acc rec) =
  st-bot-# (⊢→⊢#-step (_ , Kinding Γ⊢A∈S∙∙U) Γinert (rec _ (s≤s (≤-reflexive refl))))
⊢→⊢#-step (_ , Subtyping (st-and-l₁ Γ⊢τ₁∧τ₂∈K)) Γinert (acc rec) =
  st-and-l₁-# (⊢→⊢#-step (_ , Kinding Γ⊢τ₁∧τ₂∈K) Γinert (rec _ (s≤s (≤-reflexive refl))))
⊢→⊢#-step (_ , Subtyping (st-and-l₂ Γ⊢τ₁∧τ₂∈K)) Γinert (acc rec) =
  st-and-l₂-# (⊢→⊢#-step (_ , Kinding Γ⊢τ₁∧τ₂∈K) Γinert (rec _ (s≤s (≤-reflexive refl))))
⊢→⊢#-step (_ , Subtyping (st-and₂ Γ⊢ρ≤τ₁∈K Γ⊢ρ≤τ₂∈K)) Γinert (acc rec) =
  st-and₂-#
    (⊢→⊢#-step (_ , Subtyping Γ⊢ρ≤τ₁∈K) Γinert (rec _ (s≤s (m≤m⊔n _ _))))
    (⊢→⊢#-step (_ , Subtyping Γ⊢ρ≤τ₂∈K) Γinert (rec _ (s≤s (m≤n⊔m _ _))))
⊢→⊢#-step (_ , Subtyping (st-field Γ⊢τ₁≤τ₂∈K)) Γinert (acc rec) =
  st-field-# (⊢→⊢#-step (_ , Subtyping Γ⊢τ₁≤τ₂∈K) Γinert (rec _ (s≤s (≤-reflexive refl))))
⊢→⊢#-step (_ , Subtyping (st-typ Γ⊢J≤K)) Γinert (acc rec) =
  st-typ-# (⊢→⊢#-step (_ , Subkinding Γ⊢J≤K) Γinert (rec _ (s≤s (≤-reflexive refl))))
⊢→⊢#-step (_ , Subtyping t@(st-app Γ⊢A₁≤A₂ e@(st-antisym Γ⊢B₁≤B₂ Γ⊢B₂≤B₁))) Γinert (acc rec) =
  st-app-#
    (⊢→⊢#-step (_ , Subtyping Γ⊢A₁≤A₂) Γinert (rec _ (s≤s (m≤m⊔n _ _))))
    (st-antisym-#
      (⊢→⊢#-step (_ , Subtyping Γ⊢B₁≤B₂) Γinert (rec _ p1))
      (⊢→⊢#-step (_ , Subtyping Γ⊢B₂≤B₁) Γinert (rec _ p2)))
  where
    open Data.Nat.Properties.≤-Reasoning

    p1 : ⊢ty[]≤[]∈[]-h Γ⊢B₁≤B₂ <ℕ ⊢ty[]≤[]∈[]-h t
    p1 = begin-strict
        ⊢ty[]≤[]∈[]-h Γ⊢B₁≤B₂
      <⟨ s≤s (m≤m⊔n _ _) ⟩
        suc (⊢ty[]≤[]∈[]-h Γ⊢B₁≤B₂ ⊔ ⊢ty[]≤[]∈[]-h Γ⊢B₂≤B₁)
      <⟨ s≤s (m≤n⊔m _ _) ⟩
        suc (⊢ty[]≤[]∈[]-h Γ⊢A₁≤A₂ ⊔ ⊢ty[]==[]-h e)
      ≡⟨⟩
        ⊢ty[]≤[]∈[]-h t
      ∎

    p2 : ⊢ty[]≤[]∈[]-h Γ⊢B₂≤B₁ <ℕ ⊢ty[]≤[]∈[]-h t
    p2 = begin-strict
        ⊢ty[]≤[]∈[]-h Γ⊢B₂≤B₁
      <⟨ s≤s (m≤n⊔m _ _) ⟩
        suc (⊢ty[]≤[]∈[]-h Γ⊢B₁≤B₂ ⊔ ⊢ty[]≤[]∈[]-h Γ⊢B₂≤B₁)
      <⟨ s≤s (m≤n⊔m _ _) ⟩
        suc (⊢ty[]≤[]∈[]-h Γ⊢A₁≤A₂ ⊔ ⊢ty[]==[]-h e)
      ≡⟨⟩
        ⊢ty[]≤[]∈[]-h t
      ∎
⊢→⊢#-step (_ , Subtyping (st-bnd₁ Γ⊢A∈S∙∙U)) Γinert (acc rec) =
  st-bnd₁-# (⊢→⊢#-step (_ , Kinding Γ⊢A∈S∙∙U) Γinert (rec _ (s≤s (≤-reflexive refl))))
⊢→⊢#-step (_ , Subtyping (st-bnd₂ Γ⊢A∈S∙∙U)) Γinert (acc rec) =
  st-bnd₂-# (⊢→⊢#-step (_ , Kinding Γ⊢A∈S∙∙U) Γinert (rec _ (s≤s (≤-reflexive refl))))
⊢→⊢#-step (_ , Subtyping (st-β₁ Γ⊢A∈K Γ⊢B∈J)) = {!!}
⊢→⊢#-step (_ , Subtyping (st-β₂ Γ⊢A∈K Γ⊢B∈J)) = {!!}

⊢→⊢# : ∀ {Γ Out} → Γ inert-ctx → Judgment Γ Out → Out
⊢→⊢# {Γ} {Out} Γinert j = ⊢→⊢#-step ((Γ , Out) , j) Γinert (<-wf ((Γ , Out) , j))

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

  ⊢ty→⊢#ty : ∀ {Γ Out} → Γ inert-ctx → Judgment Γ Out → Out
  ⊢ty→⊢#ty {Γ} {Out} Γinert j = {! withMeasure PackedJudgment-height
      (λ j → unpack j)
      go
      ((Γ , Out) , j) Γinert
    where
      go : ∀ j →
        (∀ j' → PackedJudgment-height j' < PackedJudgment-height j → unpack j') →
        unpack j
      go (_ , Subtyping (st-refl Γ⊢A∈K)) rec Γinert =
        st-refl-# (rec (_ , Kinding Γ⊢A∈K) (s≤s (≤-reflexive refl)) Γinert)
      go (_ , Subtyping (st-trans Γ⊢A≤B Γ⊢B≤C)) rec Γinert =
        st-trans-#
          (rec (_ , Subtyping Γ⊢A≤B) (s≤s (m≤m⊔n _ _)) Γinert)
          (rec (_ , Subtyping Γ⊢B≤C) (s≤s (m≤n⊔m _ _)) Γinert)
      go (_ , Subtyping (st-top Γ⊢A∈S∙∙U)) rec Γinert =
        st-top-# (rec (_ , Kinding Γ⊢A∈S∙∙U) (s≤s (≤-reflexive refl)) Γinert)
      go (_ , Subtyping (st-bot Γ⊢A∈S∙∙U)) rec Γinert =
        st-bot-# (rec (_ , Kinding Γ⊢A∈S∙∙U) (s≤s (≤-reflexive refl)) Γinert)
      go (_ , Subtyping (st-and-l₁ Γ⊢τ₁∧τ₂∈K)) rec Γinert =
        st-and-l₁-# (rec (_ , Kinding Γ⊢τ₁∧τ₂∈K) (s≤s (≤-reflexive refl)) Γinert)
      go (_ , Subtyping (st-and-l₂ Γ⊢τ₁∧τ₂∈K)) rec Γinert =
        st-and-l₂-# (rec (_ , Kinding Γ⊢τ₁∧τ₂∈K) (s≤s (≤-reflexive refl)) Γinert)
      go (_ , Subtyping (st-and₂ Γ⊢ρ≤τ₁∈K Γ⊢ρ≤τ₂∈K)) rec Γinert =
        st-and₂-#
          (rec (_ , Subtyping Γ⊢ρ≤τ₁∈K) (s≤s (m≤m⊔n _ _)) Γinert)
          (rec (_ , Subtyping Γ⊢ρ≤τ₂∈K) (s≤s (m≤n⊔m _ _)) Γinert)
      go (_ , Subtyping (st-field Γ⊢τ₁≤τ₂∈K)) rec Γinert =
        st-field-# (rec (_ , Subtyping Γ⊢τ₁≤τ₂∈K) (s≤s (≤-reflexive refl)) Γinert)
      go (_ , Subtyping (st-typ Γ⊢J≤K)) rec Γinert = st-typ-# (⊢→⊢#-sk Γinert Γ⊢J≤K)
      go (_ , Subtyping t@(st-app Γ⊢A₁≤A₂ e@(st-antisym Γ⊢B₁≤B₂ Γ⊢B₂≤B₁))) rec Γinert =
        st-app-#
          (rec (_ , Subtyping Γ⊢A₁≤A₂) (s≤s (m≤m⊔n _ _)) Γinert)
          (st-antisym-#
            (rec (_ , Subtyping Γ⊢B₁≤B₂) p1 Γinert)
            (rec (_ , Subtyping Γ⊢B₂≤B₁) p2 Γinert))
        where
          open Data.Nat.Properties.≤-Reasoning

          p1 : ⊢ty[]≤[]∈[]-h Γ⊢B₁≤B₂ < ⊢ty[]≤[]∈[]-h t
          p1 = begin-strict
              ⊢ty[]≤[]∈[]-h Γ⊢B₁≤B₂
            <⟨ s≤s (m≤m⊔n _ _) ⟩
              suc (⊢ty[]≤[]∈[]-h Γ⊢B₁≤B₂ ⊔ ⊢ty[]≤[]∈[]-h Γ⊢B₂≤B₁)
            <⟨ s≤s (m≤n⊔m _ _) ⟩
              suc (⊢ty[]≤[]∈[]-h Γ⊢A₁≤A₂ ⊔ ⊢ty[]==[]-h e)
            ≡⟨⟩
              ⊢ty[]≤[]∈[]-h t
            ∎

          p2 : ⊢ty[]≤[]∈[]-h Γ⊢B₂≤B₁ < ⊢ty[]≤[]∈[]-h t
          p2 = begin-strict
              ⊢ty[]≤[]∈[]-h Γ⊢B₂≤B₁
            <⟨ s≤s (m≤n⊔m _ _) ⟩
              suc (⊢ty[]≤[]∈[]-h Γ⊢B₁≤B₂ ⊔ ⊢ty[]≤[]∈[]-h Γ⊢B₂≤B₁)
            <⟨ s≤s (m≤n⊔m _ _) ⟩
              suc (⊢ty[]≤[]∈[]-h Γ⊢A₁≤A₂ ⊔ ⊢ty[]==[]-h e)
            ≡⟨⟩
              ⊢ty[]≤[]∈[]-h t
            ∎
      go (_ , Subtyping (st-bnd₁ Γ⊢A∈S∙∙U)) rec Γinert =
        st-bnd₁-# (rec (_ , Kinding Γ⊢A∈S∙∙U) (s≤s (≤-reflexive refl)) Γinert)
      go (_ , Subtyping (st-bnd₂ Γ⊢A∈S∙∙U)) rec Γinert =
        st-bnd₂-# (rec (_ , Kinding Γ⊢A∈S∙∙U) (s≤s (≤-reflexive refl)) Γinert)
      {-
      go (_ , Subtyping (st-β₁ Γ⊢A∈K Γ⊢B∈J)) = {!!}
      go (_ , Subtyping (st-β₂ Γ⊢A∈K Γ⊢B∈J)) = {!!}
      -}
      go (_ , Subtyping p) rec Γinert = {!!}
      go (_ , Kinding (k-var Γctx Γ[x]⊢>τ)) rec Γinert =
        k-var-# (ctx-ctx# Γinert Γctx) Γ[x]⊢>τ
      go (_ , Kinding p) rec Γinert = {!!} !}

  ⊢→⊢#-st : ∀ {Γ S U k} → Γ inert-ctx → Γ ⊢ty S ≤ U ∈ k → Γ ⊢#ty S ≤ U ∈ k
  ⊢→⊢#-st Γinert p = ⊢ty→⊢#ty Γinert (Subtyping p)

  ⊢→⊢#-ty : ∀ {Γ τ k} → Γ inert-ctx → Γ ⊢ty τ ∈ k → Γ ⊢#ty τ ∈ k
  ⊢→⊢#-ty Γinert p = ⊢ty→⊢#ty Γinert (Kinding p)
  {-
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
  ⊢→⊢#-ty Γinert (k-sel Γ⊢x∈[typA∶k]) =
    let KS τ Γ⊢#τ∈k U Γ⊢!x∈[typA∶S[k]] =
          k-sel-premise Γinert (⊢→⊢#-tm Γinert Γ⊢x∈[typA∶k])
     in
    k-sub-#
      (k-sel-# Γ⊢#τ∈k Γ⊢!x∈[typA∶S[k]])
      (sing-sub Γ⊢#τ∈k)
      -}

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

