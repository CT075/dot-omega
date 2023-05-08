module Data.Context where

open import Data.Nat
open import Data.Fin
open import Data.List hiding (lookup)
open import Data.Maybe
open import Relation.Unary
open import Relation.Binary.PropositionalEquality

infix 21 _&_

data Ctx {ℓ} (T : Pred ℕ ℓ) : ℕ → Set ℓ where
  ⊘ : Ctx T zero
  _&_ : ∀{n} → Ctx T n → T n → Ctx T (suc n)

record Weaken {ℓ} (T : Pred ℕ ℓ) : Set ℓ where
  field
    weaken : ∀{n} → T n → T (suc n)

open Weaken ⦃ ... ⦄ public

lookup : ∀{ℓ} {T : Pred ℕ ℓ} ⦃ _ : Weaken T ⦄ {n} → Ctx T n → Fin n → T n
lookup ⊘ ()
lookup (Γ & τ) zero = weaken τ
lookup (Γ & τ) (suc i) = weaken (lookup Γ i)

infix 20 _[_]⊢>_

_[_]⊢>_ : ∀{ℓ} {T : Pred ℕ ℓ} ⦃ _ : Weaken T ⦄ {n} →
  Ctx T n → Fin n → T n → Set ℓ
Γ [ x ]⊢> τ = lookup Γ x ≡ τ
