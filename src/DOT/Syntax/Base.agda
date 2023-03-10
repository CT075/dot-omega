open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary using (DecSetoid)

module DOT.Syntax.Base {ℓ}
    (TypeL : DecSetoid lzero ℓ)
    (TermL : DecSetoid lzero ℓ)
  where

open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero)
open import Data.List using (List)

open import Data.Var using (Var)

TypeLabel = DecSetoid.Carrier TypeL
TermLabel = DecSetoid.Carrier TermL

mutual
  data Type : Set where
    ⊤ : Type                               -- top
    ⊥ : Type                               -- bottom
    [_] : Decl → Type                      -- record
    _∧_ : Type → Type → Type               -- intersection
    _∙_ : Var → TypeLabel → Type           -- type selection
    μ : Type → Type                        -- recursive types
    ℿ : Type → Type → Type                 -- dependent function

  data Decl : Set where
    [_∶_∙∙_] : TypeLabel → Type → Type → Decl
    [_∶_] : TermLabel → Type → Decl

mutual
  data Term : Set where
    ` : Var → Term                         -- variables
    V : Val → Term                         -- values
    _∙_ : Var → TermLabel → Term           -- field selection
    _⊡_ : Var → Var → Term                 -- application
    let'_in'_ : Term → Term → Term         -- let-binding

  data Val : Set where
    new : Type → List Defn → Val           -- new object definitions
    ƛ : Type → Term → Val                  -- lambdas

  data Defn : Set where
    [ty_='_] : TypeLabel → Type → Defn
    [tm_='_] : TermLabel → Term → Defn

mutual
  liftTerm : (Var → Term) → Term → Term
  liftTerm f (` x) = f x
  liftTerm f (V vl) = {! !}
  liftTerm f (x ∙ x₁) = {! !}
  liftTerm f (x ⊡ x₁) = {! !}
  liftTerm f (let' t in' t₁) = {! !}

foo = record { var = ` ; lift = liftTerm }
