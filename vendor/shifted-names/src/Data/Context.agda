module Data.Context where

open import Data.Nat using (ℕ; suc; zero)
open import Data.String using (String; _==_; _≟_)
open import Data.Bool using (if_then_else_)
open import Data.List using (List; []; _∷_; map)
open import Data.Empty using (⊥-elim) renaming (⊥ to Void)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Nullary using (yes; no)

open import Data.Var using (Name; N; Lift)

record Entry T : Set where
  constructor E
  field
    name : String
    typ : T

Ctx : ∀ T {{_ : Lift T}} → Set
Ctx T = List (Entry T)

empty : ∀ {T} {{_ : Lift T}} → Ctx T
empty = []

infix 21 _&_~_

shiftEntry : ∀{T} {{_ : Lift T}} → String → Entry T → Entry T
shiftEntry {{TLift}} x (E y τ) =
  if x == y then E y (Lift.shiftT TLift x τ) else E y τ

_&_~_ : ∀ {T} {{_ : Lift T}} → Ctx T → String → T → Ctx T
_&_~_ {{TLift}} Γ x τ = E x τ ∷ map (shiftEntry {{TLift}} x) Γ

infix 20 _[_]⊢>_

_[_]⊢>_ : ∀ {T} {{_ : Lift T}} → Ctx T → Name → T → Set
_[_]⊢>_ [] _ _ = Void
_[_]⊢>_ {{TLift}} (E x τ ∷ Γ) (name@(N y zero)) τ' =
  if x == y then τ ≡ τ' else Γ [ name ]⊢> τ'
_[_]⊢>_ {{TLift}} (E x τ ∷ Γ) (name@(N y (suc i))) τ' =
  if x == y then Γ [ N y i ]⊢> τ' else Γ [ name ]⊢> τ'

hd-replace-zero : ∀ {T} {{_ : Lift T}} (Γ : Ctx T) {x y τ} τ₁ τ₂ →
  (Γ & x ~ τ₁) [ N y zero ]⊢> τ → x ≢ y →
  (Γ & x ~ τ₂) [ N y zero ]⊢> τ
hd-replace-zero {_} Γ {x} {y} τ₁ τ₂ proof x≢y with x ≟ y
... | yes x≡y = ⊥-elim (x≢y x≡y)
... | no _ = proof

hd-replace-suc : ∀ {T} {{_ : Lift T}} (Γ : Ctx T) {x y i τ} τ₁ τ₂ →
  (Γ & x ~ τ₁) [ N y (suc i) ]⊢> τ →
  (Γ & x ~ τ₂) [ N y (suc i) ]⊢> τ
hd-replace-suc {_} Γ {x} {y} τ₁ τ₂ proof with x ≟ y
... | yes x≡y rewrite x≡y = proof
... | no _ = proof
