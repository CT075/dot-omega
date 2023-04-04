module Data.Context where

open import Data.Nat using (ℕ; suc; zero)
open import Data.String using (String; _==_; _≟_)
open import Data.Bool using (if_then_else_; true; false)
open import Data.List using (List; []; _∷_; map)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality
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

data _[_]⊢>_ {T} {{_ : Lift T}} : Ctx T → Name → T → Set where
  bind-hd : ∀{Γ x τ} → (E x τ ∷ Γ) [ N x zero ]⊢> τ
  bind-tl-xx : ∀{Γ x τ ρ i} →
    Γ [ N x i ]⊢> τ →
    (E x ρ ∷ Γ) [ N x (suc i) ]⊢> τ
  bind-tl-xy : ∀{Γ x y τ ρ i} →
    Γ [ N x i ]⊢> τ →
    x ≢ y →
    (E y ρ ∷ Γ) [ N x i ]⊢> τ

replace : ∀ {T} {{_ : Lift T}} (Γ : Ctx T) name {τ} →
  T → Γ [ name ]⊢> τ → Ctx T
replace {T} {{TLift}} [] _ _ ()
replace {T} {{TLift}} (E y ρ ∷ Γ) name@(N x zero) τ proof
  with x ≟ y | proof
... | yes x≡y | bind-hd = E x τ ∷ Γ
... | yes x≡y | bind-tl-xy Γ[x]⊢>τ x≢y = ⊥-elim (x≢y x≡y)
... | no x≢y | bind-hd = ⊥-elim (x≢y refl)
... | no x≢y | bind-tl-xy Γ[x]⊢>τ _ = E y ρ ∷ replace Γ name τ Γ[x]⊢>τ
replace {T} {{TLift}} (E y ρ ∷ Γ) name@(N x (suc i)) τ proof with x ≟ y | proof
... | yes x≡y | bind-tl-xx Γ[x]⊢>τ' = E y ρ ∷ replace Γ (N y i) τ Γ[x]⊢>τ'
... | yes x≡y | bind-tl-xy _ x≢y = ⊥-elim (x≢y x≡y)
... | no x≢y | bind-tl-xx _ = ⊥-elim (x≢y refl)
... | no x≢y | bind-tl-xy Γ[x]⊢>τ' _ = E y ρ ∷ replace Γ name τ Γ[x]⊢>τ'
