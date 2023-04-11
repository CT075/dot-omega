open import Level renaming (zero to lzero; suc to lsuc) hiding (Lift)
open import Relation.Binary using (DecSetoid)

module DOTOmega.Typing.Tight.Properties {ℓ}
    (TypeL : DecSetoid lzero ℓ)
    (TermL : DecSetoid lzero ℓ)
  where

open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality

open import DOTOmega.Syntax TypeL TermL
open import DOTOmega.Typing TypeL TermL
open import DOTOmega.Typing.Tight TypeL TermL
open import DOTOmega.Typing.Precise TypeL TermL

postulate
  sing-sub : ∀{Γ τ k} → Γ ⊢#ty τ ∈ k → Γ ⊢#kd S[ τ ∈ k ] ≤ k

postulate
  dec-typ-inv : ∀ {Γ x τ M k} →
    Γ ⊢!var x ∈ τ ⟫ [ typ M ∶ k ] →
    Σ[ y ∈ Type × Kind ](k ≡ (S[ proj₁ y ∈ proj₂ y ]))

