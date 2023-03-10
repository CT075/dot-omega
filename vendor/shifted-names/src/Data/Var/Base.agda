module Data.Var.Base where

open import Data.Nat using (ℕ; suc; zero)
open import Data.String using (String; _==_)
open import Data.Bool using (if_then_else_)
open import Level using (Level)
open import Relation.Unary using (Pred)

record Name : Set where
  constructor N
  field
    name : String
    index : ℕ

bump : String → Name → Name
bump x (N y i) = if x == y then N y (suc i) else N y i

lower : ∀{T : Set} → (Name → T) → T → String → Name → T
lower free bzero x (N y zero) = if x == y then bzero else free (N y zero)
lower free bzero x (N y (suc i)) = if x == y then free (N y i) else free (N y (suc i))

-- Shifted names are a variation on locally-nameless types, in which each name
-- is annotated with an index marking how many times it's been shadowed.
--
-- It's worth noting that [Bound] in this formulation uses de Bruijin _levels_
-- (0 refers to the outermost binding), not de Bruijin _indicies_ (0 refers to
-- the innermost binding). This was the numbering scheme used by Dolan and
-- repeated here, as it simplifies the operation definitions a lot.
data Var : Set where
  Bound : ℕ → Var
  Free : Name → Var

openVar : String → Var → Var
openVar x (Bound zero) = Free (N x zero)
openVar x (Bound (suc n)) = Bound n
openVar x (Free name) = Free (bump x name)

closeVar : String → Var → Var
closeVar x (Bound n) = Bound (suc n)
closeVar x (Free name) = lower Free (Bound zero) x name

wkVar : Var → Var
wkVar (Bound n) = Bound (suc n)
wkVar (Free name) = Free name

-- Simple generalization of variable-level transforms to full ASTs
record Lift {ℓ : Level} (T : Set ℓ) : Set ℓ where
  field
    lift : (Var → Var) → T → T

  openT : String → T → T
  openT x = lift (openVar x)

  closeT : String → T → T
  closeT x = lift (closeVar x)

  wkT : T → T
  wkT = lift wkVar

record Subst {ℓ : Level} (S : Set ℓ) (T : Set ℓ) : Set ℓ where
  field
    lift : Lift T
    var : Var → S
    subst : (Var → S) → T → T

  bindVar : S → Var → S
  bindVar u (Bound zero) = u
  bindVar u (Bound (suc n)) = var (Bound n)
  bindVar u (Free name) = var (Free name)

  bindT : S → T → T
  bindT u = subst (bindVar u)

{-
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
  bind u (Free name) = var (Free name)

  apply : Op T → Var → T
  apply (Open x) v = var (open' x v)
  apply (Close x) v = var (closeVar x v)
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
-}
