open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary using (DecSetoid)

module DOT.Syntax {ℓ}
    (TypeL : DecSetoid lzero ℓ)
    (TermL : DecSetoid lzero ℓ)
  where

open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero)
open import Data.String using (String)
open import Data.List using (List)

open import Data.Var using (Var)

TypeLabel = DecSetoid.Carrier TypeL
TermLabel = DecSetoid.Carrier TermL

data Label : Set where
  Ty : TypeLabel → Label
  Tm : TermLabel → Label

mutual
  data Type (n : ℕ) : Set where
    ⊤ : Type n                            -- top
    ⊥ : Type n                            -- bottom
    [_] : Decl n → Type n                 -- record
    _∧_ : Type n → Type n → Type n        -- intersection
    _∙_ : Var n → TypeLabel → Type n      -- type selection
    μ : Type (suc n) → Type n             -- recursive types
    ℿ : Type n → Type (suc n) → Type n    -- dependent function

  data Decl (n : ℕ) : Set where
    [_∶_∙∙_] : TypeLabel → Type n → Type n → Decl n
    [_∶_] : TermLabel → Type n → Decl n

mutual
  data Term (n : ℕ) : Set where
    ` : Var n → Term n                    -- variables
    V : Val n → Term n                    -- values
    _∙_ : Var n → TermLabel → Term n      -- field selection
    _⊡_ : Var n → Var n → Term n          -- application
    let'_in'_ : Term n → Term (suc n) → Term n -- let-binding

  data Val (n : ℕ) : Set where
    new : Type n → List (Defn n) → Val n  -- new object definitions
    ƛ : Type n → Term (suc n) → Val n     -- lambdas

  data Defn (n : ℕ) : Set where
    [ty_='_] : TypeLabel → Type n → Defn n
    [tm_='_] : TermLabel → Term n → Defn n

