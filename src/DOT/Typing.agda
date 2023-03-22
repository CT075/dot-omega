open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary using (DecSetoid)

-- General typing rules for DOT. Adapted from Marianna Rapoport's Simple DOT
-- proof here:
-- https://amaurremi.github.io/dot-calculus/src/simple-proof/doc/Definitions.html

module DOT.Typing {ℓ}
    (TypeL : DecSetoid lzero ℓ)
    (TermL : DecSetoid lzero ℓ)
  where

open import Data.List using (List; []; _∷_; map)

open import Data.Var

open import DOT.Syntax TypeL TermL

open import Data.Context

infix 4 _⊢tm_∈_
infix 4 _⊢ty_≤_
infix 4 _⊢defn_∈_ _⊢defns_∈_

mutual
  -- Term typing
  data _⊢tm_∈_ : Ctx Type → Term → Type → Set where
    ty-var : ∀{Γ name τ} → Γ [ name ]⊢> τ → Γ ⊢tm `(Free name) ∈ τ
    ty-ℿ-intro : ∀{Γ x τ ρ e} →
      Γ & x ~ τ ⊢tm openTerm x e ∈ openType x ρ →
      Γ ⊢tm V(ƛ τ e) ∈ ℿ τ ρ
    ty-ℿ-elim : ∀{Γ x z τ ρ} →
      Γ ⊢tm ` x ∈ ℿ τ ρ → Γ ⊢tm ` z ∈ τ →
      Γ ⊢tm x ⊡ z ∈ bindType z ρ
    ty-new-intro : ∀{Γ τ x ds} →
      Γ & x ~ (openType x τ) ⊢defns (map (openDefn x) ds) ∈ (openType x τ) →
      Γ ⊢tm V(new τ ds) ∈ μ τ
    ty-new-elim : ∀{Γ x ℓ τ} →
      Γ ⊢tm ` x ∈ [ val ℓ ∶ τ ] →
      Γ ⊢tm x ∙ ℓ ∈ τ
    ty-let : ∀{Γ e₁ e₂ x τ ρ} →
      Γ ⊢tm e₁ ∈ τ →
      Γ & x ~ τ ⊢tm (openTerm x e₂) ∈ ρ →
      Γ ⊢tm (let' e₁ in' e₂) ∈ ρ
    ty-rec-intro : ∀{Γ x τ} →
      Γ ⊢tm ` x ∈ bindType x τ →
      Γ ⊢tm ` x ∈ μ τ
    ty-rec-elim : ∀{Γ x τ} →
      Γ ⊢tm ` x ∈ μ τ →
      Γ ⊢tm ` x ∈ bindType x τ
    ty-and-intro : ∀{Γ x τ₁ τ₂} →
      Γ ⊢tm ` x ∈ τ₁ → Γ ⊢tm ` x ∈ τ₂ →
      Γ ⊢tm ` x ∈ τ₁ ∧ τ₂
    ty-sub : ∀{Γ e τ₁ τ₂} →
      Γ ⊢tm e ∈ τ₁ → Γ ⊢ty τ₁ ≤ τ₂ →
      Γ ⊢tm e ∈ τ₂

  -- Definition typing
  data _⊢defn_∈_ : Ctx Type → Defn → Decl → Set where
    ty-defn-type : ∀{Γ A τ} → Γ ⊢defn (typ A =' τ) ∈ typ A ∶ τ ∙∙ τ
    ty-defn-term : ∀{Γ ℓ e τ} →
      Γ ⊢tm e ∈ τ →
      Γ ⊢defn (val ℓ =' e) ∈ val ℓ ∶ τ

  data _⊢defns_∈_ : Ctx Type → List Defn → Type → Set where
    ty-defns-one : ∀{Γ d D} →
      Γ ⊢defn d ∈ D →
      Γ ⊢defns (d ∷ []) ∈ [ D ]
    ty-defns-cons : ∀{Γ d ds D τ} →
      Γ ⊢defns ds ∈ τ →
      Γ ⊢defn d ∈ D →
      d ∉ ds →
      Γ ⊢defns (d ∷ ds) ∈ τ ∧ [ D ]

  -- Subtyping
  data _⊢ty_≤_ : Ctx Type → Type → Type → Set where
    st-top : ∀{Γ τ} → Γ ⊢ty τ ≤ ⊤
    st-bot : ∀{Γ τ} → Γ ⊢ty ⊥ ≤ τ
    st-refl : ∀{Γ τ} → Γ ⊢ty τ ≤ τ
    st-trans : ∀{Γ ρ τ₁ τ₂} →
      Γ ⊢ty τ₁ ≤ ρ → Γ ⊢ty ρ ≤ τ₂ →
      Γ ⊢ty τ₁ ≤ τ₂
    st-and-l₁ : ∀{Γ τ₁ τ₂} → Γ ⊢ty τ₁ ∧ τ₂ ≤ τ₁
    st-and-l₂ : ∀{Γ τ₁ τ₂} → Γ ⊢ty τ₁ ∧ τ₂ ≤ τ₂
    st-and₂ : ∀{Γ ρ τ₁ τ₂} →
      Γ ⊢ty ρ ≤ τ₁ → Γ ⊢ty ρ ≤ τ₂ →
      Γ ⊢ty ρ ≤ τ₁ ∧ τ₂
    st-field : ∀{Γ ℓ τ₁ τ₂} →
      Γ ⊢ty τ₁ ≤ τ₂ →
      Γ ⊢ty [ val ℓ ∶ τ₁ ] ≤ [ val ℓ ∶ τ₂ ]
    st-typ : ∀{Γ A τ₁ ρ₁ τ₂ ρ₂} →
      Γ ⊢ty ρ₁ ≤ τ₁ → Γ ⊢ty τ₂ ≤ ρ₂ →
      Γ ⊢ty [ typ A ∶ τ₁ ∙∙ τ₂ ] ≤ [ typ A ∶ ρ₁ ∙∙ ρ₂ ]
    st-sel₁ : ∀{Γ x A τ₁ τ₂} →
      Γ ⊢tm ` x ∈ [ typ A ∶ τ₁ ∙∙ τ₂ ] →
      Γ ⊢ty τ₁ ≤ x ∙ A
    st-sel₂ : ∀{Γ x A τ₁ τ₂} →
      Γ ⊢tm ` x ∈ [ typ A ∶ τ₁ ∙∙ τ₂ ] →
      Γ ⊢ty x ∙ A ≤ τ₂
    st-ℿ : ∀{Γ x τ₁ τ₂ ρ₁ ρ₂} →
      Γ ⊢ty ρ₁ ≤ τ₁ →
      Γ & x ~ ρ₁ ⊢ty openType x τ₂ ≤ openType x ρ₂ →
      Γ ⊢ty ℿ τ₁ τ₂ ≤ ℿ ρ₁ ρ₂

