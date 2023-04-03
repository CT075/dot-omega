module Data.Context.Properties where

open import Data.Nat using (ℕ; suc; zero)
open import Data.String using (String; _==_; _≟_)
open import Data.Bool using (if_then_else_; true; false)
open import Data.List using (List; []; _∷_; map)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (yes; no)

open import Data.Var
open import Data.Context

open ≡-Reasoning

replace-spec-xx : ∀ {T} {{_ : Lift T}} (Γ : Ctx T) name τ {τ'} →
  (name∈Γ : Γ [ name ]⊢> τ') →
  replace Γ name τ (name∈Γ) [ name ]⊢> τ
replace-spec-xx {T} {{TLift}} [] _ _ ()
replace-spec-xx {T} {{TLift}} (E x ρ ∷ Γ) name@(N y zero) τ name∈Γ
  with x ≟ y | name∈Γ
... | yes x≡y | bind-hd = {!!}
  where
    foo : replace (E x ρ ∷ Γ) (N x zero) τ bind-hd ≡ E x τ ∷ Γ
    foo = begin
        replace (E x ρ ∷ Γ) (N x zero) τ bind-hd
      ≡⟨ refl ⟩
        {!!}
      ≡⟨ refl ⟩
        E x τ ∷ Γ
      ∎
... | yes x≡y | bind-tl-xy _ y≢x = ⊥-elim (y≢x (sym x≡y))
... | no x≢y | bind-hd = ⊥-elim (x≢y refl)
... | no x≢y | bind-tl-xy Γ[y]⊢>τ' y≢x = {!!}
replace-spec-xx {T} {{TLift}} (E x ρ ∷ Γ) name@(N y (suc i)) τ name∈Γ = {!!}
