open import Level renaming (zero to lzero; suc to lsuc) hiding (Lift)
open import Relation.Binary using (DecSetoid)

module DOTOmega.Typing.Invertible.Properties
    (TypeL : DecSetoid lzero lzero)
    (TermL : DecSetoid lzero lzero)
  where

open import DOTOmega.Syntax TypeL TermL
open import DOTOmega.Typing.Tight TypeL TermL
open import DOTOmega.Typing.Tight.Properties TypeL TermL
open import DOTOmega.Typing.Precise TypeL TermL
open import DOTOmega.Typing.Invertible TypeL TermL

postulate
  -- proof: by induction on [Γ ⊢#ty A ≤ B]
  invertible-typing-closure-tight-var : ∀{Γ x A B} →
    Γ ⊢##var x ∈ A →
    Γ ⊢#ty A ≤ B ∈ ✶ →
    Γ ⊢##var x ∈ B

  invertible-typing-closure-tight-val : ∀{Γ v A B} →
    Γ ⊢##val v ∈ A →
    Γ ⊢#ty A ≤ B ∈ ✶ →
    Γ ⊢##val v ∈ B

  ⊢##→⊢#-var : ∀{Γ x τ} → Γ ⊢##var x ∈ τ → Γ ⊢#tm ` x ∈ τ

⊢#→⊢##-var : ∀{Γ x τ} → Γ inert-ctx → Γ ⊢#tm ` x ∈ τ → Γ ⊢##var x ∈ τ
⊢#→⊢##-var Γinert (ty-var-# Γ[x]⊢>τ) = ty-precise-## (var-! Γ[x]⊢>τ)
⊢#→⊢##-var Γinert (ty-rec-intro-# Γ⊢x∈xτ) =
  ty-rec-i-## (⊢#→⊢##-var Γinert Γ⊢x∈xτ)
-- TODO: this
⊢#→⊢##-var {Γ} {x} Γinert (ty-rec-elim-# {τ = τ} Γ⊢x∈τ) = foo
  where
    postulate
      foo : Γ ⊢##var x ∈ bindType (` x) τ
⊢#→⊢##-var Γinert (ty-and-intro-# Γ⊢x∈τ₁ Γ⊢x∈τ₂) =
  ty-intersect-##
    (⊢#→⊢##-var Γinert Γ⊢x∈τ₁)
    (⊢#→⊢##-var Γinert Γ⊢x∈τ₂)
⊢#→⊢##-var Γinert (ty-sub-# Γ⊢x∈τ₁ Γ⊢τ₁≤τ₂) =
  invertible-typing-closure-tight-var
    (⊢#→⊢##-var Γinert Γ⊢x∈τ₁)
    Γ⊢τ₁≤τ₂

⊢#→⊢##-val : ∀{Γ v τ} → Γ inert-ctx → Γ ⊢#tm V v ∈ τ → Γ ⊢##val v ∈ τ
⊢#→⊢##-val Γinert (ty-ℿ-intro-# Γ,x∈τ⊢e∈ρ) = val-ty-## (fun-I-! Γ,x∈τ⊢e∈ρ)
⊢#→⊢##-val Γinert (ty-new-intro-# Γ⊢defs∈τ) = val-ty-## (rec-I-! Γ⊢defs∈τ)
⊢#→⊢##-val Γinert (ty-sub-# Γ⊢v∈τ₁ Γ⊢τ₁≤τ₂) =
  invertible-typing-closure-tight-val
    (⊢#→⊢##-val Γinert Γ⊢v∈τ₁)
    Γ⊢τ₁≤τ₂
