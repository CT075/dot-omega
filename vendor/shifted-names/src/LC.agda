module LC where

open import Data.Var

data Term : Set where
  V : Var → Term
  _∙_ : Term → Term → Term
  ƛ : Term → Term

lift : (Var → Term) → Term → Term
lift f (V v) = f v
lift f (a ∙ b) = lift f a ∙ lift f b
lift f (ƛ t) = ƛ (lift f t)

open MakeOps (record { var = V ; lift = lift }) hiding (lift) public

infix 4 _∼>_

data _∼>_ : Term → Term → Set where
  -- If you know you have a bound variable that wants to be immediately
  -- substituted, you can just use [Bind] directly
  β : ∀ {t₁ t₂} → (ƛ t₁) ∙ t₂ ∼> (t₁ / Bind t₂)

