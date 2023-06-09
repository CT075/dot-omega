open import Level renaming (zero to lzero; suc to lsuc) hiding (Lift)
open import Relation.Binary using (DecSetoid)

module DOTOmega.Typing.Tight.Properties
    (TypeL : DecSetoid lzero lzero)
    (TermL : DecSetoid lzero lzero)
  where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality

open import DOTOmega.Syntax TypeL TermL hiding (_∉_; _∈_)
open import DOTOmega.Typing TypeL TermL
open import DOTOmega.Typing.Inertness TypeL TermL
open import DOTOmega.Typing.Tight TypeL TermL renaming (_⊢#ty_≤_∈_ to R_⊢#ty_≤_∈_)
open import DOTOmega.Typing.Precise TypeL TermL

open import Data.Context

module View where
  data _⊢#ty_≤_∈_ (Γ : Context) : Type → Type → Kind → Set where
    view-st-refl-# : ∀{K A} → Γ ⊢#ty A ∈ K → Γ ⊢#ty A ≤ A ∈ K
    view-st-trans-# : ∀{K A B C} →
      Γ ⊢#ty A ≤ B ∈ K →
      Γ ⊢#ty B ≤ C ∈ K →
      Γ ⊢#ty A ≤ C ∈ K
    view-st-top-# : ∀{A B C} → Γ ⊢#ty A ∈ B ∙∙ C → Γ ⊢#ty A ≤ ⊤ ∈ ✶
    view-st-bot-# : ∀{A B C} → Γ ⊢#ty A ∈ B ∙∙ C → Γ ⊢#ty ⊥ ≤ A ∈ ✶
    view-st-and-l₁-# : ∀{τ₁ τ₂ K} → Γ ⊢#ty τ₁ ∧ τ₂ ∈ K → Γ ⊢#ty τ₁ ∧ τ₂ ≤ τ₁ ∈ K
    view-st-and-l₂-# : ∀{τ₁ τ₂ K} → Γ ⊢#ty τ₁ ∧ τ₂ ∈ K → Γ ⊢#ty τ₁ ∧ τ₂ ≤ τ₂ ∈ K
    view-st-and₂-# : ∀{ρ τ₁ τ₂ K} →
      Γ ⊢#ty ρ ≤ τ₁ ∈ K → Γ ⊢#ty ρ ≤ τ₂ ∈ K →
      Γ ⊢#ty ρ ≤ τ₁ ∧ τ₂ ∈ K
    view-st-abs-# : ∀{x S₁ S₂ T₁ T₂} →
      Γ ⊢#ty S₂ ≤ S₁ ∈ ✶ →
      Γ & x ~ Ty S₂ ⊢ty openType x T₁ ≤ openType x T₂ ∈ ✶ →
      Γ ⊢#ty ℿ S₁ T₁ ≤ ℿ S₂ T₂ ∈ ✶
    view-st-field-# : ∀{ℓ τ₁ τ₂ k} →
      Γ ⊢#ty τ₁ ≤ τ₂ ∈ k →
      Γ ⊢#ty [ val ℓ ∶ τ₁ ] ≤ [ val ℓ ∶ τ₂ ] ∈ ✶
    view-st-typ-# : ∀{A k₁ k₂} →
      Γ ⊢#kd k₁ ≤ k₂ →
      Γ ⊢#ty [ typ A ∶ k₁ ] ≤ [ typ A ∶ k₂ ] ∈ ✶
    view-st-β₁-# : ∀{J K x A B BA BK} →
      Γ ⊢#ty B ∈ J →
      Γ & x ~ Kd (S[ B ∈ J ]) ⊢#ty openType x A ∈ openKind x K →
      BK ≡ bindKind B K →
      BA ≡ bindType B A →
      Γ ⊢#ty (ƛ J A) ⊡ B ≤ BA ∈ BK
    view-st-β₂-# : ∀{J K x A B BA BK} →
      Γ ⊢#ty B ∈ J →
      Γ & x ~ Kd (S[ B ∈ J ]) ⊢#ty openType x A ∈ openKind x K →
      BK ≡ bindKind B K →
      BA ≡ bindType B A →
      Γ ⊢#ty BA ≤ (ƛ J A) ⊡ B ∈ BK
    view-st-app-# : ∀{A₁ A₂ B₁ B₂ J K B₁K} →
      Γ ⊢#ty A₁ ≤ A₂ ∈ ℿ J K →
      Γ ⊢#ty B₁ == B₂ ∈ J →
      B₁K ≡ bindKind B₁ K →
      Γ ⊢#ty A₁ ⊡ A₂ ≤ B₁ ⊡ B₂ ∈ B₁K
    view-st-bnd₁-# : ∀{A S U} → Γ ⊢#ty A ∈ S ∙∙ U → Γ ⊢#ty S ≤ A ∈ ✶
    view-st-bnd₂-# : ∀{A S U} → Γ ⊢#ty A ∈ S ∙∙ U → Γ ⊢#ty A ≤ U ∈ ✶

  to-view : ∀{Γ A B K} → R Γ ⊢#ty A ≤ B ∈ K → Γ ⊢#ty A ≤ B ∈ K
  to-view (st-refl-# Γ⊢#A∈K) = view-st-refl-# Γ⊢#A∈K
  to-view (st-trans-# RΓ⊢#A≤B∈K RΓ⊢#B≤C∈K) =
    view-st-trans-# (to-view RΓ⊢#A≤B∈K) (to-view RΓ⊢#B≤C∈K)
  to-view (st-top-# Γ⊢#A∈S∙∙U) = view-st-top-# Γ⊢#A∈S∙∙U
  to-view (st-bot-# Γ⊢#A∈S∙∙U) = view-st-bot-# Γ⊢#A∈S∙∙U
  to-view (st-and-l₁-# Γ⊢#A∈S∧U) = view-st-and-l₁-# Γ⊢#A∈S∧U
  to-view (st-and-l₂-# Γ⊢#A∈S∧U) = view-st-and-l₂-# Γ⊢#A∈S∧U
  to-view (st-and₂-# RΓ⊢#τ≤S∈K RΓ⊢#τ≤U∈K) =
    view-st-and₂-# (to-view RΓ⊢#τ≤S∈K) (to-view RΓ⊢#τ≤U∈K)
  to-view (st-abs-# RΓ⊢#A₂≤A₁ Γx⊢B₁≤B₂) = view-st-abs-# (to-view RΓ⊢#A₂≤A₁) Γx⊢B₁≤B₂
  to-view (st-field-# RΓ⊢#A≤B∈✶) = view-st-field-# (to-view RΓ⊢#A≤B∈✶)
  to-view (st-typ-# Γ⊢#J≤K) = view-st-typ-# Γ⊢#J≤K
  to-view (st-β₁-# Γ⊢#B∈J Γx⊢#A∈K) = view-st-β₁-# Γ⊢#B∈J Γx⊢#A∈K refl refl
  to-view (st-β₂-# Γ⊢#B∈J Γx⊢#A∈K) = view-st-β₂-# Γ⊢#B∈J Γx⊢#A∈K refl refl
  to-view (st-app-# RΓ⊢#tyA₁≤A₂∈K Γ⊢B₁==B₂) =
    view-st-app-# (to-view RΓ⊢#tyA₁≤A₂∈K) Γ⊢B₁==B₂ refl
  to-view (st-bnd₁-# Γ⊢#A∈S∙∙U) = view-st-bnd₁-# Γ⊢#A∈S∙∙U
  to-view (st-bnd₂-# Γ⊢#A∈S∙∙U) = view-st-bnd₂-# Γ⊢#A∈S∙∙U

  of-view : ∀{Γ A B K} → Γ ⊢#ty A ≤ B ∈ K → R Γ ⊢#ty A ≤ B ∈ K
  of-view (view-st-refl-# Γ⊢#A∈K) = st-refl-# Γ⊢#A∈K
  of-view (view-st-trans-# RΓ⊢#A≤B∈K RΓ⊢#B≤C∈K) =
    st-trans-# (of-view RΓ⊢#A≤B∈K) (of-view RΓ⊢#B≤C∈K)
  of-view (view-st-top-# Γ⊢#A∈S∙∙U) = st-top-# Γ⊢#A∈S∙∙U
  of-view (view-st-bot-# Γ⊢#A∈S∙∙U) = st-bot-# Γ⊢#A∈S∙∙U
  of-view (view-st-and-l₁-# Γ⊢#A∈S∧U) = st-and-l₁-# Γ⊢#A∈S∧U
  of-view (view-st-and-l₂-# Γ⊢#A∈S∧U) = st-and-l₂-# Γ⊢#A∈S∧U
  of-view (view-st-and₂-# RΓ⊢#τ≤S∈K RΓ⊢#τ≤U∈K) =
    st-and₂-# (of-view RΓ⊢#τ≤S∈K) (of-view RΓ⊢#τ≤U∈K)
  of-view (view-st-abs-# RΓ⊢#A₂≤A₁ Γx⊢B₁≤B₂) = st-abs-# (of-view RΓ⊢#A₂≤A₁) Γx⊢B₁≤B₂
  of-view (view-st-field-# RΓ⊢#A≤B∈✶) = st-field-# (of-view RΓ⊢#A≤B∈✶)
  of-view (view-st-typ-# Γ⊢#J≤K) = st-typ-# Γ⊢#J≤K
  of-view (view-st-β₁-# Γ⊢#B∈J Γx⊢#A∈K refl refl) = st-β₁-# Γ⊢#B∈J Γx⊢#A∈K
  of-view (view-st-β₂-# Γ⊢#B∈J Γx⊢#A∈K refl refl) = st-β₂-# Γ⊢#B∈J Γx⊢#A∈K
  of-view (view-st-app-# RΓ⊢#tyA₁≤A₂∈K Γ⊢B₁==B₂ refl) =
    st-app-# (of-view RΓ⊢#tyA₁≤A₂∈K) Γ⊢B₁==B₂
  of-view (view-st-bnd₁-# Γ⊢#A∈S∙∙U) = st-bnd₁-# Γ⊢#A∈S∙∙U
  of-view (view-st-bnd₂-# Γ⊢#A∈S∙∙U) = st-bnd₂-# Γ⊢#A∈S∙∙U

open View renaming (_⊢#ty_≤_∈_ to _sees_≤_∈_) public

private
  _⊢#ty_≤_∈_ = R_⊢#ty_≤_∈_

postulate
  plug-recd : ∀ {z τ} → τ recd → plugType z τ recd

  sing-sub : ∀{Γ τ k} → Γ ⊢ty τ ∈ k → Γ ⊢kd S[ τ ∈ k ] ≤ k

  sing-sub-# : ∀{Γ τ k} → Γ ⊢#ty τ ∈ k → Γ ⊢#kd S[ τ ∈ k ] ≤ k

  sing-idempotent : ∀ τ K → S[ τ ∈ S[ τ ∈ K ] ] ≡ S[ τ ∈ K ]

  sing-inert : ∀ τ k → S[ τ ∈ k ] inert-kd

  sing-trans-#-l : ∀{Γ τ K J} → Γ ⊢#kd K ≤ J → Γ ⊢#kd S[ τ ∈ K ] ≤ S[ τ ∈ J ]

  sk-trans-# : ∀{Γ J K L} → Γ ⊢#kd J ≤ K → Γ ⊢#kd K ≤ L → Γ ⊢#kd J ≤ L

  -- probably need kind validity here as well
  sk-refl-# : ∀{Γ} K → Γ ⊢#kd K ≤ K

  types-wf-# : ∀{Γ t τ} → Γ ⊢#tm t ∈ τ → Σ[ K ∈ Kind ] (Γ ⊢#ty τ ∈ K)

  ty-refl-# : ∀{Γ A K} → Γ ⊢#ty A ∈ K → Γ ⊢#ty A == A ∈ K

  -- TODO: is this even true?
  proper-types-equality-# :
    ∀{Γ A B S U} → Γ ⊢#ty A == B ∈ S ∙∙ U → Γ ⊢#ty A == B ∈ ✶

  eq-narrow-# : ∀{Γ A B K} → Γ ⊢#ty A == B ∈ K → Γ ⊢#ty A == B ∈ S[ A ∈ K ]

eq-left-# : ∀{Γ A B K} → Γ ⊢#ty A == B ∈ K → Γ ⊢#ty A ≤ B ∈ K
eq-left-# (st-antisym-# A≤B B≤A) = A≤B

eq-right-# : ∀{Γ A B K} → Γ ⊢#ty A == B ∈ K → Γ ⊢#ty B ≤ A ∈ K
eq-right-# (st-antisym-# A≤B B≤A) = B≤A

eq-refl-# : ∀{Γ A K} → Γ ⊢#ty A ∈ K → Γ ⊢#ty A == A ∈ K
eq-refl-# Γ⊢#A∈K = st-antisym-# (st-refl-# Γ⊢#A∈K) (st-refl-# Γ⊢#A∈K)
