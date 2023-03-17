open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary using (DecSetoid)

module DOT.Typing {ℓ}
    (TypeL : DecSetoid lzero ℓ)
    (TermL : DecSetoid lzero ℓ)
  where

open import Data.List using (List; []; _∷_; map)

open import Data.Var
open import Data.Context

open import DOT.Syntax TypeL TermL

infix 4 _⊢ty_∈_
infix 4 _⊢defn_∈_
infix 4 _⊢defns_∈_

mutual
  data _⊢ty_∈_ : Ctx Type → Term → Type → Set where
    ty-var : ∀{Γ name τ} → Γ [ name ]⊢> τ → Γ ⊢ty `(Free name) ∈ τ
    ty-ℿ-intro : ∀{Γ x τ ρ e} →
      Γ & x ~ τ ⊢ty openTerm x e ∈ openType x ρ →
      Γ ⊢ty V(ƛ τ e) ∈ ℿ τ ρ
    ty-ℿ-elim : ∀{Γ x z τ ρ} →
      Γ ⊢ty ` x ∈ ℿ τ ρ → Γ ⊢ty ` z ∈ τ →
      Γ ⊢ty (x ⊡ z) ∈ (bindType z ρ)
    ty-new-intro : ∀{Γ τ x ds} →
      Γ & x ~ (openType x τ) ⊢defns (map (openDefn x) ds) ∈ (openType x τ) →
      Γ ⊢ty V(new τ ds) ∈ μ τ
    ty-let : ∀{Γ e₁ e₂ x τ ρ} →
      Γ & x ~ τ ⊢ty (openTerm x e₂) ∈ ρ →
      Γ ⊢ty (let' e₁ in' e₂) ∈ ρ

  data _⊢defn_∈_ : Ctx Type → Defn → Decl → Set where
    ty-defn-type : ∀{Γ A τ} →
      Γ ⊢defn (typ A =' τ) ∈ [ A ∶ τ ∙∙ τ ]
    ty-defn-term : ∀{Γ ℓ e τ} →
      Γ ⊢ty e ∈ τ →
      Γ ⊢defn (val ℓ =' e) ∈ [ ℓ ∶ τ ]

  data _⊢defns_∈_ : Ctx Type → List Defn → Type → Set where
    ty-defns-one : ∀{Γ d D} →
      Γ ⊢defn d ∈ D →
      Γ ⊢defns (d ∷ []) ∈ [ D ]
    ty-defns-cons : ∀{Γ d ds D τ} →
      Γ ⊢defns ds ∈ τ →
      Γ ⊢defn d ∈ D →
      -- TODO: check that d is not in ds
      Γ ⊢defns (d ∷ ds) ∈ τ ∧ [ D ]

