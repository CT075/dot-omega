module Data.Var.Base where

open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero)
open import Data.String using (String; _==_)
open import Data.Bool using (if_then_else_)
open import Level using (Level)
open import Relation.Unary using (Pred)

data Var (n : ℕ) : Set where
  Bound : Fin n → Var n
  Free : String → ℕ → Var n

open' : ∀{n} → String → Var (suc n) → Var n
open' x (Bound zero) = Free x zero
open' x (Bound (suc n)) = Bound n
open' x (Free y i) = if x == y then Free y (suc i) else Free y i

close : ∀{n} → String → Var n → Var (suc n)
close x (Bound n) = Bound (suc n)
close x (Free y zero) = if x == y then Bound zero else Free y zero
close x (Free y (suc n)) = if x == y then Free y n else Free y (suc n)

wk : ∀{n} → Var n → Var (suc n)
wk (Bound n) = Bound (suc n)
wk (Free x i) = Free x i

record Subst {ℓ : Level} (T : Pred ℕ ℓ) : Set ℓ where
  field
    var : ∀{n} → Var n → T n

  bind : ∀{n} → T n → Var (suc n) → T n
  bind u (Bound zero) = u
  bind u (Bound (suc n)) = var (Bound n)
  bind u (Free x i) = var (Free x i)

