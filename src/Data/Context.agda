open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary using (DecSetoid)

module Data.Context where

open import Data.Nat using (ℕ; suc; zero)
open import Data.String using (String)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≢_)

open import Data.Var using (Name; N)

record Entry (T : Set) : Set where
  constructor E
  field
    name : String
    typ : T

Ctx : Set → Set
Ctx T = List (Entry T)

empty : ∀{T} → Ctx T
empty = []

infix 21 _&_~_

pattern _&_~_ Γ x τ = E x τ ∷ Γ

infix 20 _[_]⊢>_

data _[_]⊢>_ {T} : Ctx T → Name → T → Set where
  bind-hd : ∀{x τ Γ} → (Γ & x ~ τ) [ N x zero ]⊢> τ
  -- TODO: These are wrong; we need to shift all occurrences of x and y in τ
  bind-tl-xx : ∀{x τ Γ i} →
    Γ [ N x i ]⊢> τ → (Γ & x ~ τ) [ N x (suc i) ]⊢> τ
  bind-tl-xy : ∀{x y τ τ' Γ i} →
    Γ [ N x i ]⊢> τ → x ≢ y → (Γ & y ~ τ') [ N x i ]⊢> τ
