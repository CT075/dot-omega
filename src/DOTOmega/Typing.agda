open import Level renaming (zero to lzero; suc to lsuc) hiding (Lift; _⊔_)
open import Relation.Binary using (DecSetoid)

module DOTOmega.Typing {ℓ}
    (TypeL : DecSetoid lzero ℓ)
    (TermL : DecSetoid lzero ℓ)
  where

open import Data.Nat using (ℕ; _⊔_; zero; suc)
open import Data.List using (List; []; _∷_; map)

open import Data.Var

open import DOTOmega.Syntax TypeL TermL

open import Data.Context

data VarFact : Set where
  Kd : Kind → VarFact              -- Type variable kind assignment
  Ty : Type → VarFact              -- Term variable type assignment

liftVarFact : (Var → Var) → VarFact → VarFact
liftVarFact f (Kd k) = Kd (liftKind f k)
liftVarFact f (Ty τ) = Ty (liftType f τ)

instance
  VarFactLift : Lift VarFact
  VarFactLift = record {lift = liftVarFact}

Context = Ctx VarFact

infix 4 _ctx
infix 4 _⊢_kd
infix 4 _⊢ty_∈_
infix 4 _⊢kd_≤_ _⊢ty_≤_∈_
infix 4 _⊢ty_==_∈_

infix 4 _⊢tm_∈_
infix 4 _⊢defn_∈_ _⊢defns_∈_

-- Regular typing

mutual
  data _ctx : Context → Set where
    c-empty : [] ctx
    c-cons-kd : ∀{Γ x k} → Γ ctx → Γ ⊢ k kd → Γ & x ~ Kd k ctx
    c-cons-ty : ∀{Γ x τ k} → Γ ctx → Γ ⊢ty τ ∈ k → Γ & x ~ Ty τ ctx

  data _⊢_kd (Γ : Context) : Kind → Set where
    wf-intv : ∀{A B} → Γ ⊢ty A ∈ ✶ → Γ ⊢ty B ∈ ✶ → Γ ⊢ A ∙∙ B kd
    wf-darr : ∀{x J K} →
      Γ ⊢ J kd →
      Γ & x ~ Kd J ⊢ (openKind x K) kd →
      Γ ⊢ ℿ J K kd

  data _⊢ty_∈_ (Γ : Context) : Type → Kind → Set where
    k-var : ∀{name k} → Γ ctx → Γ [ name ]⊢> Kd k → Γ ⊢ty `(Free name) ∈ k
    k-top : Γ ⊢ty ⊤ ∈ ✶
    k-bot : Γ ⊢ty ⊥ ∈ ✶
    k-sing : ∀{A B C} →
      Γ ⊢ty A ∈ B ∙∙ C →
      Γ ⊢ty A ∈ A ∙∙ A
    k-arr : ∀{x A B} →
      Γ ⊢ty A ∈ ✶ →
      Γ & x ~ Ty A ⊢ty openType x B ∈ ✶ →
      Γ ⊢ty ℿ A B ∈ ✶
    k-abs : ∀{x J K A} →
      Γ ⊢ J kd →
      Γ & x ~ Kd J ⊢ty openType x A ∈ openKind x K →
      Γ ⊢ty ƛ J A ∈ ℿ J K
    k-app : ∀{J K f τ} →
      Γ ⊢ty f ∈ ℿ J K →
      Γ ⊢ty τ ∈ J →
      Γ ⊢ty f ⊡ τ ∈ bindKind τ K
    k-intersect : ∀{τ₁ τ₂ S₁ U₁ S₂ U₂} →
      Γ ⊢ty τ₁ ∈ S₁ ∙∙ U₁ →
      Γ ⊢ty τ₂ ∈ S₂ ∙∙ U₂ →
      -- TODO: lower bound should be union
      Γ ⊢ty τ₁ ∧ τ₂ ∈ S₁ ∧ S₂ ∙∙ U₁ ∧ U₂
    k-sub : ∀{J K A} →
      Γ ⊢ty A ∈ J → Γ ⊢kd J ≤ K →
      Γ ⊢ty A ∈ K
    k-field : ∀{ℓ τ A B} →
      Γ ⊢ty τ ∈ A ∙∙ B →
      Γ ⊢ty [ val ℓ ∶ τ ] ∈ ✶
    k-typ : ∀{A k} →
      Γ ⊢ k kd →
      Γ ⊢ty [ typ A ∶ k ] ∈ ✶
    k-sel : ∀{A x k} →
      Γ ⊢tm ` x ∈ [ typ A ∶ k ] →
      Γ ⊢ty x ∙ A ∈ k

  data _⊢kd_≤_ (Γ : Context) : Kind → Kind → Set where
    sk-intv : ∀{A₁ A₂ B₁ B₂} →
      Γ ⊢ty A₂ ≤ A₁ ∈ ✶ →
      Γ ⊢ty B₁ ≤ B₂ ∈ ✶ →
      Γ ⊢kd A₁ ∙∙ B₁ ≤ A₂ ∙∙ B₂
    sk-darr : ∀{x J₁ J₂ K₁ K₂} →
      Γ ⊢ ℿ J₁ K₁ kd →
      Γ ⊢kd J₂ ≤ J₁ →
      Γ & x ~ Kd J₂ ⊢kd openKind x K₁ ≤ openKind x K₂ →
      Γ ⊢kd ℿ J₁ K₁ ≤ ℿ J₂ K₂

  data _⊢ty_≤_∈_ (Γ : Context) : Type → Type → Kind → Set where
    st-refl : ∀{K A} → Γ ⊢ty A ∈ K → Γ ⊢ty A ≤ A ∈ K
    st-trans : ∀{K A B C} →
      Γ ⊢ty A ≤ B ∈ K →
      Γ ⊢ty B ≤ C ∈ K →
      Γ ⊢ty A ≤ C ∈ K
    st-top : ∀{A B C} → Γ ⊢ty A ∈ B ∙∙ C → Γ ⊢ty A ≤ ⊤ ∈ ✶
    st-bot : ∀{A B C} → Γ ⊢ty A ∈ B ∙∙ C → Γ ⊢ty ⊥ ≤ A ∈ ✶
    st-and-l₁ : ∀{τ₁ τ₂ K} → Γ ⊢ty τ₁ ∧ τ₂ ∈ K → Γ ⊢ty τ₁ ∧ τ₂ ≤ τ₁ ∈ K
    st-and-l₂ : ∀{τ₁ τ₂ K} → Γ ⊢ty τ₁ ∧ τ₂ ∈ K → Γ ⊢ty τ₁ ∧ τ₂ ≤ τ₂ ∈ K
    st-and₂ : ∀{ρ τ₁ τ₂ K} →
      Γ ⊢ty ρ ≤ τ₁ ∈ K → Γ ⊢ty ρ ≤ τ₂ ∈ K →
      Γ ⊢ty ρ ≤ τ₁ ∧ τ₂ ∈ K
    st-field : ∀{ℓ τ₁ τ₂ k} →
      Γ ⊢ty τ₁ ≤ τ₂ ∈ k →
      Γ ⊢ty [ val ℓ ∶ τ₁ ] ≤ [ val ℓ ∶ τ₂ ] ∈ ✶
    st-typ : ∀{A k₁ k₂} →
      Γ ⊢kd k₁ ≤ k₂ →
      Γ ⊢ty [ typ A ∶ k₁ ] ≤ [ typ A ∶ k₂ ] ∈ ✶
    st-β₁ : ∀{J K x A B} →
      Γ & x ~ Kd J ⊢ty openType x A ∈ K →
      Γ ⊢ty B ∈ J →
      Γ ⊢ty (ƛ J A) ⊡ B ≤ bindType B A ∈ bindKind B K
    st-β₂ : ∀{J K x A B} →
      Γ & x ~ Kd J ⊢ty openType x A ∈ K →
      Γ ⊢ty B ∈ J →
      Γ ⊢ty bindType B A ≤ (ƛ J A) ⊡ B ∈ bindKind B K
    st-app : ∀{A₁ A₂ B₁ B₂ J K} →
      Γ ⊢ty A₁ ≤ A₂ ∈ ℿ J K →
      Γ ⊢ty B₁ == B₂ ∈ J →
      Γ ⊢ty A₁ ⊡ A₂ ≤ B₁ ⊡ B₂ ∈ bindKind B₁ K
    st-bnd₁ : ∀{A S U} → Γ ⊢ty A ∈ S ∙∙ U → Γ ⊢ty S ≤ A ∈ ✶
    st-bnd₂ : ∀{A S U} → Γ ⊢ty A ∈ S ∙∙ U → Γ ⊢ty A ≤ U ∈ ✶

  -- Type equality
  data _⊢ty_==_∈_ (Γ : Context) : Type → Type → Kind → Set where
    st-antisym : ∀{K A B} →
      Γ ⊢ty A ≤ B ∈ K → Γ ⊢ty B ≤ A ∈ K → Γ ⊢ty A == B ∈ K

  data _⊢tm_∈_ (Γ : Ctx VarFact) : Term → Type → Set where
    ty-var : ∀{name τ} → Γ [ name ]⊢> Ty τ → Γ ⊢tm `(Free name) ∈ τ
    ty-ℿ-intro : ∀{x τ ρ e} →
      Γ & x ~ Ty τ ⊢tm openTerm x e ∈ openType x ρ →
      Γ ⊢tm V(ƛ τ e) ∈ ℿ τ ρ
    ty-ℿ-elim : ∀{x z τ ρ} →
      Γ ⊢tm ` x ∈ ℿ τ ρ → Γ ⊢tm ` z ∈ τ →
      Γ ⊢tm x ⊡ z ∈ bindType (` z) ρ
    ty-new-intro : ∀{τ x ds} →
      Γ & x ~ Ty (openType x τ) ⊢defns (map (openDefn x) ds) ∈ (openType x τ) →
      Γ ⊢tm V(new τ ds) ∈ μ τ
    ty-new-elim : ∀{x ℓ τ} →
      Γ ⊢tm ` x ∈ [ val ℓ ∶ τ ] →
      Γ ⊢tm x ∙ ℓ ∈ τ
    ty-let : ∀{e₁ e₂ x τ ρ} →
      Γ ⊢tm e₁ ∈ τ →
      Γ & x ~ Ty τ ⊢tm (openTerm x e₂) ∈ ρ →
      Γ ⊢tm (let' e₁ in' e₂) ∈ ρ
    ty-rec-intro : ∀{x τ} →
      Γ ⊢tm ` x ∈ bindType (` x) τ →
      Γ ⊢tm ` x ∈ μ τ
    ty-rec-elim : ∀{x τ} →
      Γ ⊢tm ` x ∈ μ τ →
      Γ ⊢tm ` x ∈ bindType (` x) τ
    ty-and-intro : ∀{x τ₁ τ₂} →
      Γ ⊢tm ` x ∈ τ₁ → Γ ⊢tm ` x ∈ τ₂ →
      Γ ⊢tm ` x ∈ τ₁ ∧ τ₂
    ty-sub : ∀{e τ₁ τ₂} →
      Γ ⊢tm e ∈ τ₁ → Γ ⊢ty τ₁ ≤ τ₂ ∈ ✶ →
      Γ ⊢tm e ∈ τ₂

  -- Definition typing
  data _⊢defn_∈_ (Γ : Ctx VarFact) : Defn → Decl → Set where
    ty-defn-type : ∀{M k τ} →
      Γ ⊢ty τ ∈ k →
      -- TODO: this should be S(τ : K)
      Γ ⊢defn (typ M =' τ) ∈ typ M ∶ τ ∙∙ τ
    ty-defn-term : ∀{ℓ e τ} →
      Γ ⊢tm e ∈ τ →
      Γ ⊢defn (val ℓ =' e) ∈ val ℓ ∶ τ

  data _⊢defns_∈_ (Γ : Ctx VarFact) : List Defn → Type → Set where
    ty-defns-one : ∀{d D} →
      Γ ⊢defn d ∈ D →
      Γ ⊢defns (d ∷ []) ∈ [ D ]
    ty-defns-cons : ∀{d ds D τ} →
      Γ ⊢defns ds ∈ τ →
      Γ ⊢defn d ∈ D →
      d ∉ ds →
      Γ ⊢defns (d ∷ ds) ∈ τ ∧ [ D ]

-- Lemmas/derived rules

intv≤✶ : ∀{Γ A B τ₁ τ₂ τ₃ τ₄} →
  Γ ⊢ty A ∈ τ₁ ∙∙ τ₂ → Γ ⊢ty B ∈ τ₃ ∙∙ τ₄ → Γ ⊢kd A ∙∙ B ≤ ✶
intv≤✶ Γ⊢A∈∙∙ Γ⊢B∈∙∙ = sk-intv (st-bot Γ⊢A∈∙∙) (st-top Γ⊢B∈∙∙)

-- Induction measures

-- TODO: this is all boilerplate, maybe replace with sized types

mutual
  []ctx-h : ∀{Γ} → Γ ctx → ℕ
  []ctx-h c-empty = 1
  []ctx-h (c-cons-kd Γctx Γ⊢Kkd) = suc ([]ctx-h Γctx ⊔ ⊢[]kd-h Γ⊢Kkd)
  []ctx-h (c-cons-ty Γctx Γ⊢τ∈k) = suc ([]ctx-h Γctx ⊔ ⊢ty[]∈[]-h Γ⊢τ∈k)

  ⊢[]kd-h : ∀{Γ k} → Γ ⊢ k kd → ℕ
  ⊢[]kd-h (wf-intv Γ⊢S∈✶ Γ⊢U∈✶) = suc (⊢ty[]∈[]-h Γ⊢S∈✶ ⊔ ⊢ty[]∈[]-h Γ⊢U∈✶)
  ⊢[]kd-h (wf-darr Γ⊢Jkd Γx⊢Kkd) = suc (⊢[]kd-h Γ⊢Jkd ⊔ ⊢[]kd-h Γx⊢Kkd)

  ⊢kd[]≤[]-h : ∀{Γ J K} → Γ ⊢kd J ≤ K → ℕ
  ⊢kd[]≤[]-h (sk-intv Γ⊢S₂≤S₁ Γ⊢U₁≤U₂) =
    suc (⊢ty[]≤[]∈[]-h Γ⊢S₂≤S₁ ⊔ ⊢ty[]≤[]∈[]-h Γ⊢U₁≤U₂)
  ⊢kd[]≤[]-h (sk-darr Γ⊢ℿJ₁K₁kd Γ⊢J₂≤J₁ Γx⊢K₁≤K₂) =
    suc (⊢[]kd-h Γ⊢ℿJ₁K₁kd ⊔ ⊢kd[]≤[]-h Γ⊢J₂≤J₁ ⊔ ⊢kd[]≤[]-h Γx⊢K₁≤K₂)

  ⊢ty[]∈[]-h : ∀{Γ τ K} → Γ ⊢ty τ ∈ K → ℕ
  ⊢ty[]∈[]-h (k-var Γctx Γ[x]⊢τ) = suc ([]ctx-h Γctx)
  ⊢ty[]∈[]-h k-top = 1
  ⊢ty[]∈[]-h k-bot = 1
  ⊢ty[]∈[]-h (k-sing Γ⊢A∈S∙∙U) = suc (⊢ty[]∈[]-h Γ⊢A∈S∙∙U)
  ⊢ty[]∈[]-h (k-arr Γ⊢A∈✶ Γ⊢B∈✶) = suc (⊢ty[]∈[]-h Γ⊢A∈✶ ⊔ ⊢ty[]∈[]-h Γ⊢B∈✶)
  ⊢ty[]∈[]-h (k-abs Γ⊢Jkd Γx⊢A∈K) = suc (⊢[]kd-h Γ⊢Jkd ⊔ ⊢ty[]∈[]-h Γx⊢A∈K)
  ⊢ty[]∈[]-h (k-app Γ⊢f∈ℿJK Γ⊢τ∈J) = suc (⊢ty[]∈[]-h Γ⊢f∈ℿJK ⊔ ⊢ty[]∈[]-h Γ⊢τ∈J)
  ⊢ty[]∈[]-h (k-intersect Γ⊢A∈K₁ Γ⊢A∈K₂) =
    suc (⊢ty[]∈[]-h Γ⊢A∈K₁ ⊔ ⊢ty[]∈[]-h Γ⊢A∈K₂)
  ⊢ty[]∈[]-h (k-sub Γ⊢A∈J Γ⊢J≤K) = suc (⊢ty[]∈[]-h Γ⊢A∈J ⊔ ⊢kd[]≤[]-h Γ⊢J≤K)
  ⊢ty[]∈[]-h (k-field Γ⊢τ∈S∙∙U) = suc (⊢ty[]∈[]-h Γ⊢τ∈S∙∙U)
  ⊢ty[]∈[]-h (k-typ Γ⊢Kkd) = suc (⊢[]kd-h Γ⊢Kkd)
  ⊢ty[]∈[]-h (k-sel Γ⊢x∈[M∶k]) = suc (⊢tm[]∈[]-h Γ⊢x∈[M∶k])

  ⊢ty[]≤[]∈[]-h : ∀{Γ A B K} → Γ ⊢ty A ≤ B ∈ K → ℕ
  ⊢ty[]≤[]∈[]-h (st-refl Γ⊢A∈K) = suc (⊢ty[]∈[]-h Γ⊢A∈K)
  ⊢ty[]≤[]∈[]-h (st-trans Γ⊢A≤B Γ⊢B≤C) =
    suc (⊢ty[]≤[]∈[]-h Γ⊢A≤B ⊔ ⊢ty[]≤[]∈[]-h Γ⊢B≤C)
  ⊢ty[]≤[]∈[]-h (st-top Γ⊢A∈✶) = suc (⊢ty[]∈[]-h Γ⊢A∈✶)
  ⊢ty[]≤[]∈[]-h (st-bot Γ⊢A∈✶) = suc (⊢ty[]∈[]-h Γ⊢A∈✶)
  ⊢ty[]≤[]∈[]-h (st-and-l₁ Γ⊢τ₁∧τ₂∈K) = suc (⊢ty[]∈[]-h Γ⊢τ₁∧τ₂∈K)
  ⊢ty[]≤[]∈[]-h (st-and-l₂ Γ⊢τ₁∧τ₂∈K) = suc (⊢ty[]∈[]-h Γ⊢τ₁∧τ₂∈K)
  ⊢ty[]≤[]∈[]-h (st-and₂ Γ⊢ρ≤τ₁ Γ⊢ρ≤τ₂) =
    suc (⊢ty[]≤[]∈[]-h Γ⊢ρ≤τ₁ ⊔ ⊢ty[]≤[]∈[]-h Γ⊢ρ≤τ₂)
  ⊢ty[]≤[]∈[]-h (st-field Γ⊢τ₁≤τ₂) = suc (⊢ty[]≤[]∈[]-h Γ⊢τ₁≤τ₂)
  ⊢ty[]≤[]∈[]-h (st-typ Γ⊢J≤K) = suc (⊢kd[]≤[]-h Γ⊢J≤K)
  ⊢ty[]≤[]∈[]-h (st-β₁ Γx⊢A∈K Γ⊢B∈J) = suc (⊢ty[]∈[]-h Γx⊢A∈K ⊔ ⊢ty[]∈[]-h Γ⊢B∈J)
  ⊢ty[]≤[]∈[]-h (st-β₂ Γx⊢A∈K Γ⊢B∈J) = suc (⊢ty[]∈[]-h Γx⊢A∈K ⊔ ⊢ty[]∈[]-h Γ⊢B∈J)
  ⊢ty[]≤[]∈[]-h (st-app Γ⊢A₁≤A₂ Γ⊢B₁==B₂) =
    suc (⊢ty[]≤[]∈[]-h Γ⊢A₁≤A₂ ⊔ ⊢ty[]==[]-h Γ⊢B₁==B₂)
  ⊢ty[]≤[]∈[]-h (st-bnd₁ Γ⊢τ∈S∙∙U) = suc (⊢ty[]∈[]-h Γ⊢τ∈S∙∙U)
  ⊢ty[]≤[]∈[]-h (st-bnd₂ Γ⊢τ∈S∙∙U) = suc (⊢ty[]∈[]-h Γ⊢τ∈S∙∙U)

  ⊢ty[]==[]-h : ∀{Γ A B K} → Γ ⊢ty A == B ∈ K → ℕ
  ⊢ty[]==[]-h (st-antisym Γ⊢A≤B Γ⊢B≤A) =
    suc (⊢ty[]≤[]∈[]-h Γ⊢A≤B ⊔ ⊢ty[]≤[]∈[]-h Γ⊢B≤A)

  ⊢tm[]∈[]-h : ∀{Γ t τ} → Γ ⊢tm t ∈ τ → ℕ
  ⊢tm[]∈[]-h (ty-var Γ[x]⊢>τ) = 1
  ⊢tm[]∈[]-h (ty-ℿ-intro Γx⊢e∈ρ) = suc (⊢tm[]∈[]-h Γx⊢e∈ρ)
  ⊢tm[]∈[]-h (ty-ℿ-elim Γ⊢f∈ℿτρ Γ⊢x∈τ) =
    suc (⊢tm[]∈[]-h Γ⊢f∈ℿτρ ⊔ ⊢tm[]∈[]-h Γ⊢x∈τ)
  ⊢tm[]∈[]-h (ty-new-intro Γ⊢ds∈τ) = ⊢defns[]∈[]-h Γ⊢ds∈τ
  ⊢tm[]∈[]-h (ty-new-elim Γ⊢x∈[ℓ∶τ]) = suc (⊢tm[]∈[]-h Γ⊢x∈[ℓ∶τ])
  ⊢tm[]∈[]-h (ty-let Γ⊢e₁∈τ Γx⊢e₂∈ρ) =
    suc (⊢tm[]∈[]-h Γ⊢e₁∈τ ⊔ ⊢tm[]∈[]-h Γx⊢e₂∈ρ)
  ⊢tm[]∈[]-h (ty-rec-intro Γ⊢x∈xτ) = suc (⊢tm[]∈[]-h Γ⊢x∈xτ)
  ⊢tm[]∈[]-h (ty-rec-elim Γ⊢x∈μτ) = suc (⊢tm[]∈[]-h Γ⊢x∈μτ)
  ⊢tm[]∈[]-h (ty-and-intro Γ⊢x∈τ₁ Γ⊢x∈τ₂) =
    suc (⊢tm[]∈[]-h Γ⊢x∈τ₁ ⊔ ⊢tm[]∈[]-h Γ⊢x∈τ₂)
  ⊢tm[]∈[]-h (ty-sub Γ⊢x∈S Γ⊢S≤U) = suc (⊢tm[]∈[]-h Γ⊢x∈S ⊔ ⊢ty[]≤[]∈[]-h Γ⊢S≤U)

  ⊢defn[]∈[]-h : ∀{Γ d τ} → Γ ⊢defn d ∈ τ → ℕ
  ⊢defn[]∈[]-h (ty-defn-type Γ⊢τ∈k) = suc (⊢ty[]∈[]-h Γ⊢τ∈k)
  ⊢defn[]∈[]-h (ty-defn-term Γ⊢e∈τ) = suc (⊢tm[]∈[]-h Γ⊢e∈τ)

  ⊢defns[]∈[]-h : ∀{Γ ds τ} → Γ ⊢defns ds ∈ τ → ℕ
  ⊢defns[]∈[]-h (ty-defns-one Γ⊢d∈τ) = suc (⊢defn[]∈[]-h Γ⊢d∈τ)
  ⊢defns[]∈[]-h (ty-defns-cons Γ⊢ds∈τ Γ⊢d∈D d∉ds) =
    suc (⊢defns[]∈[]-h Γ⊢ds∈τ ⊔ ⊢defn[]∈[]-h Γ⊢d∈D)
