open import Level renaming (zero to lzero; suc to lsuc) hiding (Lift)
open import Relation.Binary using (DecSetoid)

module DOTOmega.Typing.Tight {ℓ}
    (TypeL : DecSetoid lzero ℓ)
    (TermL : DecSetoid lzero ℓ)
  where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; map)

open import DOTOmega.Syntax TypeL TermL
open import DOTOmega.Typing TypeL TermL
open import DOTOmega.Typing.Precise TypeL TermL

open import Data.Var
open import Data.Context

infix 4 _⊢#_kd
infix 4 _⊢#ty_∈_
infix 4 _⊢#kd_≤_ _⊢#ty_≤_∈_
infix 4 _⊢#ty_==_∈_

infix 4 _⊢#tm_∈_

infix 4 _inert-kd _inert-ty _inert-ctx

data _inert-kd : Kind → Set where
  intv-inert : ∀ {A} → A ∙∙ A inert-kd
  pi-inert : ∀ {J K} → K inert-kd → ℿ J K inert-kd

data _inert-ty : Type → Set where
  pi-inert : ∀ {τ₁ τ₂} → ℿ τ₁ τ₂ inert-ty
  -- TODO: inert records

data _inert-ctx : Context → Set where
  empty-inert : [] inert-ctx
  cons-inert-ty : ∀ {Γ x τ} → Γ inert-ctx → τ inert-ty → Γ & x ~ Ty τ inert-ctx
  cons-inert-kd : ∀ {Γ x k} → Γ inert-ctx → k inert-kd → Γ & x ~ Kd k inert-ctx

S[_∈_] : Type → Kind → Kind
S[ τ ∈ A ∙∙ B ] = τ ∙∙ τ
S[ f ∈ ℿ J K ] = ℿ J (S[ f ⊡ `(Bound zero) ∈ K ])

mutual
  data _ctx-# : Context → Set where
    c-empty-# : [] ctx-#
    c-cons-kd-# : ∀{Γ x k} → Γ ctx-# → Γ ⊢# k kd → Γ & x ~ Kd k ctx-#
    c-cons-ty-# : ∀{Γ x τ k} → Γ ctx-# → Γ ⊢#ty τ ∈ k → Γ & x ~ Ty τ ctx-#

  data _⊢#_kd (Γ : Context) : Kind → Set where
    wf-intv-# : ∀{A B} → Γ ⊢#ty A ∈ ✶ → Γ ⊢#ty B ∈ ✶ → Γ ⊢# A ∙∙ B kd
    wf-darr-# : ∀{x J K} →
      Γ ⊢# J kd →
      Γ & x ~ Kd J ⊢ (openKind x K) kd →
      Γ ⊢# ℿ J K kd

  data _⊢#ty_∈_ (Γ : Context) : Type → Kind → Set where
    k-var-# : ∀{name k} → Γ ctx-# → Γ [ name ]⊢> Kd k → Γ ⊢#ty `(Free name) ∈ k
    k-top-# : Γ ⊢#ty ⊤ ∈ ✶
    k-bot-# : Γ ⊢#ty ⊥ ∈ ✶
    k-sing-# : ∀{A B C} →
      Γ ⊢#ty A ∈ B ∙∙ C →
      Γ ⊢#ty A ∈ A ∙∙ A
    k-arr-# : ∀{x A B} →
      Γ ⊢#ty A ∈ ✶ →
      Γ & x ~ Ty A ⊢ty openType x B ∈ ✶ →
      Γ ⊢#ty ℿ A B ∈ ✶
    k-abs-# : ∀{x J K A} →
      Γ ⊢# J kd →
      Γ & x ~ Kd J ⊢ty openType x A ∈ openKind x K →
      Γ ⊢#ty ƛ J A ∈ ℿ J K
    k-app-# : ∀{J K f τ} →
      Γ ⊢#ty f ∈ ℿ J K →
      Γ ⊢#ty τ ∈ J →
      Γ ⊢#ty f ⊡ τ ∈ bindKind τ K
    k-intersect-# : ∀{τ₁ τ₂ S₁ U₁ S₂ U₂} →
      Γ ⊢#ty τ₁ ∈ S₁ ∙∙ U₁ →
      Γ ⊢#ty τ₂ ∈ S₂ ∙∙ U₂ →
      -- TODO: lower bound should be union
      Γ ⊢#ty τ₁ ∧ τ₂ ∈ S₁ ∧ S₂ ∙∙ U₁ ∧ U₂
    k-sub-# : ∀{J K A} →
      Γ ⊢#ty A ∈ J → Γ ⊢#kd J ≤ K →
      Γ ⊢#ty A ∈ K
    k-field-# : ∀{ℓ τ A B} →
      Γ ⊢#ty τ ∈ A ∙∙ B →
      Γ ⊢#ty [ val ℓ ∶ τ ] ∈ ✶
    k-typ-# : ∀{A k} →
      Γ ⊢# k kd →
      Γ ⊢#ty [ typ A ∶ k ] ∈ ✶
    k-sel-# : ∀{A x U τ k} →
      Γ ⊢#ty τ ∈ k →
      Γ ⊢!var x ∈ U ⟫ [ typ A ∶ S[ τ ∈ k ] ] →
      Γ ⊢#ty x ∙ A ∈ S[ τ ∈ k ]

  data _⊢#kd_≤_ (Γ : Context) : Kind → Kind → Set where
    sk-intv-# : ∀{A₁ A₂ B₁ B₂} →
      Γ ⊢#ty A₂ ≤ A₁ ∈ ✶ →
      Γ ⊢#ty B₁ ≤ B₂ ∈ ✶ →
      Γ ⊢#kd A₁ ∙∙ B₁ ≤ A₂ ∙∙ B₂
    sk-darr-# : ∀{x J₁ J₂ K₁ K₂} →
      Γ ⊢# ℿ J₁ K₁ kd →
      Γ ⊢#kd J₂ ≤ J₁ →
      Γ & x ~ Kd J₂ ⊢kd openKind x K₁ ≤ openKind x K₂ →
      Γ ⊢#kd ℿ J₁ K₁ ≤ ℿ J₂ K₂

  data _⊢#ty_≤_∈_ (Γ : Context) : Type → Type → Kind → Set where
    st-refl-# : ∀{K A} → Γ ⊢#ty A ∈ K → Γ ⊢#ty A ≤ A ∈ K
    st-trans-# : ∀{K A B C} →
      Γ ⊢#ty A ≤ B ∈ K →
      Γ ⊢#ty B ≤ C ∈ K →
      Γ ⊢#ty A ≤ C ∈ K
    st-top-# : ∀{A B C} → Γ ⊢#ty A ∈ B ∙∙ C → Γ ⊢#ty A ≤ ⊤ ∈ ✶
    st-bot-# : ∀{A B C} → Γ ⊢#ty A ∈ B ∙∙ C → Γ ⊢#ty ⊥ ≤ A ∈ ✶
    st-and-l₁-# : ∀{τ₁ τ₂ K} → Γ ⊢#ty τ₁ ∧ τ₂ ∈ K → Γ ⊢#ty τ₁ ∧ τ₂ ≤ τ₁ ∈ K
    st-and-l₂-# : ∀{τ₁ τ₂ K} → Γ ⊢#ty τ₁ ∧ τ₂ ∈ K → Γ ⊢#ty τ₁ ∧ τ₂ ≤ τ₂ ∈ K
    st-and₂-# : ∀{ρ τ₁ τ₂ K} →
      Γ ⊢#ty ρ ≤ τ₁ ∈ K → Γ ⊢#ty ρ ≤ τ₂ ∈ K →
      Γ ⊢#ty ρ ≤ τ₁ ∧ τ₂ ∈ K
    st-field-# : ∀{ℓ τ₁ τ₂ k} →
      Γ ⊢#ty τ₁ ≤ τ₂ ∈ k →
      Γ ⊢#ty [ val ℓ ∶ τ₁ ] ≤ [ val ℓ ∶ τ₂ ] ∈ ✶
    st-typ-# : ∀{A k₁ k₂} →
      Γ ⊢#kd k₁ ≤ k₂ →
      Γ ⊢#ty [ typ A ∶ k₁ ] ≤ [ typ A ∶ k₂ ] ∈ ✶
    st-β₁-# : ∀{J K x A B} →
      Γ ⊢#ty B ∈ J →
      Γ & x ~ Kd (S[ B ∈ J ]) ⊢#ty openType x A ∈ K →
      Γ ⊢#ty (ƛ J A) ⊡ B ≤ bindType B A ∈ bindKind B K
    st-β₂-# : ∀{J K x A B} →
      Γ ⊢#ty B ∈ J →
      Γ & x ~ Kd (S[ B ∈ J ]) ⊢#ty openType x A ∈ K →
      Γ ⊢#ty bindType B A ≤ (ƛ J A) ⊡ B ∈ bindKind B K
    st-app-# : ∀{A₁ A₂ B₁ B₂ J K} →
      Γ ⊢#ty A₁ ≤ A₂ ∈ ℿ J K →
      Γ ⊢#ty B₁ == B₂ ∈ J →
      Γ ⊢#ty A₁ ⊡ A₂ ≤ B₁ ⊡ B₂ ∈ bindKind B₁ K
    st-bnd₁-# : ∀{A S U} → Γ ⊢#ty A ∈ S ∙∙ U → Γ ⊢#ty S ≤ A ∈ ✶
    st-bnd₂-# : ∀{A S U} → Γ ⊢#ty A ∈ S ∙∙ U → Γ ⊢#ty A ≤ U ∈ ✶

  -- Type equality
  data _⊢#ty_==_∈_ (Γ : Context) : Type → Type → Kind → Set where
    st-antisym-# : ∀{K A B} →
      Γ ⊢#ty A ≤ B ∈ K → Γ ⊢#ty B ≤ A ∈ K → Γ ⊢#ty A == B ∈ K

  data _⊢#tm_∈_ (Γ : Ctx VarFact) : Term → Type → Set where
    ty-var-# : ∀{name τ} → Γ [ name ]⊢> Ty τ → Γ ⊢#tm `(Free name) ∈ τ
    ty-ℿ-intro-# : ∀{x τ ρ e} →
      Γ & x ~ Ty τ ⊢tm openTerm x e ∈ openType x ρ →
      Γ ⊢#tm V(ƛ τ e) ∈ ℿ τ ρ
    ty-ℿ-elim-# : ∀{x z τ ρ} →
      Γ ⊢#tm ` x ∈ ℿ τ ρ → Γ ⊢#tm ` z ∈ τ →
      Γ ⊢#tm x ⊡ z ∈ bindType (` z) ρ
    ty-new-intro-# : ∀{τ x ds} →
      Γ & x ~ Ty (openType x τ) ⊢defns (map (openDefn x) ds) ∈ (openType x τ) →
      Γ ⊢#tm V(new τ ds) ∈ μ τ
    ty-new-elim-# : ∀{x ℓ τ} →
      Γ ⊢#tm ` x ∈ [ val ℓ ∶ τ ] →
      Γ ⊢#tm x ∙ ℓ ∈ τ
    ty-let-# : ∀{e₁ e₂ x τ ρ} →
      Γ ⊢#tm e₁ ∈ τ →
      Γ & x ~ Ty τ ⊢tm (openTerm x e₂) ∈ ρ →
      Γ ⊢#tm (let' e₁ in' e₂) ∈ ρ
    ty-rec-intro-# : ∀{x τ} →
      Γ ⊢#tm ` x ∈ bindType (` x) τ →
      Γ ⊢#tm ` x ∈ μ τ
    ty-rec-elim-# : ∀{x τ} →
      Γ ⊢#tm ` x ∈ μ τ →
      Γ ⊢#tm ` x ∈ bindType (` x) τ
    ty-and-intro-# : ∀{x τ₁ τ₂} →
      Γ ⊢#tm ` x ∈ τ₁ → Γ ⊢#tm ` x ∈ τ₂ →
      Γ ⊢#tm ` x ∈ τ₁ ∧ τ₂
    ty-sub-# : ∀{e τ₁ τ₂} →
      Γ ⊢#tm e ∈ τ₁ → Γ ⊢#ty τ₁ ≤ τ₂ ∈ ✶ →
      Γ ⊢#tm e ∈ τ₂