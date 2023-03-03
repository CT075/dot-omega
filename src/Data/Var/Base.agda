module Data.Var.Base where

open import Data.Nat using (ℕ; suc; zero)
open import Data.String using (String; _==_)
open import Data.Bool using (if_then_else_)
open import Level using (Level)
open import Relation.Unary using (Pred)

-- Shifted names are a variation on locally-nameless types, in which each name
-- is annotated with an index marking how many times it's been shadowed.
--
-- It's worth noting that [Bound] in this formulation uses de Bruijin _levels_
-- (0 refers to the outermost binding), not de Bruijin _indicies_ (0 refers to
-- the innermost binding). This was the numbering scheme used by Dolan and
-- repeated here, as it simplifies the operation definitions a lot.
data Var : Set where
  Bound : ℕ → Var
  Free : String → ℕ → Var

open' : String → Var → Var
open' x (Bound zero) = Free x zero
open' x (Bound (suc n)) = Bound n
open' x (Free y i) = if x == y then Free y (suc i) else Free y i

close : String → Var → Var
close x (Bound n) = Bound (suc n)
close x (Free y zero) = if x == y then Bound zero else Free y zero
close x (Free y (suc n)) = if x == y then Free y n else Free y (suc n)

wk : Var → Var
wk (Bound n) = Bound (suc n)
wk (Free x i) = Free x i

data Op {ℓ : Level} (T : Set ℓ) : Set ℓ where
  Open : String → Op T
  Close : String → Op T
  Wk : Op T
  Bind : T → Op T
  _∘_ : Op T → Op T → Op T

record MakeOps {ℓ : Level} (T : Set ℓ) : Set ℓ where
  field
    var : Var → T
    lift : (Var → T) → T → T

  bind : T → Var → T
  bind u (Bound zero) = u
  bind u (Bound (suc n)) = var (Bound n)
  bind u (Free x i) = var (Free x i)

  apply : Op T → Var → T
  apply (Open x) v = var (open' x v)
  apply (Close x) v = var (close x v)
  apply Wk v = var (wk v)
  apply (Bind u) v = bind u v
  apply (op₂ ∘ op₁) v = lift (apply op₂) (apply op₁ v)

  _/_ : T → Op T → T
  t / op = lift (apply op) t

  infix 4 Rename_to_

  -- Compound operations
  Rename_to_ : String → String → Op T
  Rename x to y = Open y ∘ Close x

  Subst : T → String → Op T
  Subst u x = Bind u ∘ Close x

  Shift : String -> Op T
  Shift x = Open x ∘ Wk

