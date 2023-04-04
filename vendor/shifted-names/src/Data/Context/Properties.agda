module Data.Context.Properties where

open import Function using (_∘_)
open import Data.Nat using (ℕ; suc; zero)
open import Data.String using (String; _==_; _≟_)
open import Data.Bool using (if_then_else_; true; false; Bool)
open import Data.List using (List; []; _∷_; map)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (yes; no)

open import Data.Var
open import Data.Context

open ≡-Reasoning

extract-N-x-≡ : ∀ {x y i j} → N x i ≡ N y j → x ≡ y
extract-N-x-≡ {x} {.x} refl = refl

extract-N-i-≡ : ∀ {x y i j} → N x i ≡ N y j → i ≡ j
extract-N-i-≡ {x} {.x} refl = refl

replace-spec-xx : ∀ {T} {{_ : Lift T}} (Γ : Ctx T) name τ {τ'} →
  (name∈Γ : Γ [ name ]⊢> τ') →
  replace Γ name τ name∈Γ [ name ]⊢> τ
replace-spec-xx {T} {{TLift}} (E y ρ ∷ Γ) name@(N x zero) τ name∈Γ
  with x ≟ y | name∈Γ
... | yes x≡y | bind-hd = bind-hd
... | yes x≡y | bind-tl-xy _ x≢y = ⊥-elim (x≢y x≡y)
... | no x≢y | bind-hd = ⊥-elim (x≢y refl)
... | no x≢y | bind-tl-xy Γ[x]⊢>τ' x≢y =
  bind-tl-xy (replace-spec-xx Γ (N x zero) τ Γ[x]⊢>τ') x≢y
replace-spec-xx {T} {{TLift}} (E y ρ ∷ Γ) name@(N x (suc i)) τ name∈Γ
  with x ≟ y | name∈Γ
... | yes x≡y | bind-tl-xx Γ[x]⊢>τ' =
  bind-tl-xx (replace-spec-xx Γ (N x i) τ Γ[x]⊢>τ')
... | yes x≡y | bind-tl-xy _ x≢y = ⊥-elim (x≢y x≡y)
... | no x≢y | bind-tl-xx Γ[x]⊢>τ' = ⊥-elim (x≢y refl)
... | no x≢y | bind-tl-xy Γ[x]⊢>τ' _ =
  bind-tl-xy (replace-spec-xx Γ name τ Γ[x]⊢>τ') x≢y

replace-spec-xy : ∀ {T} {{_ : Lift T}} (Γ : Ctx T) name name' τ τ' →
  (name∈Γ : Γ [ name ]⊢> τ) →
  (name'∈Γ : Γ [ name' ]⊢> τ') →
  name ≢ name' →
  replace Γ name τ name∈Γ [ name' ]⊢> τ'
replace-spec-xy {T} {{TLift}}
    (E y ρ ∷ Γ)
    name@(N x zero)
    name'@(N x' i')
    τ τ'
    name∈Γ name'∈Γ
    name≢name'
  with x ≟ y | name∈Γ | name'∈Γ
... | _ | bind-hd | bind-hd = ⊥-elim (name≢name' refl)
... | yes x≡y | bind-hd | bind-tl-xx Γ[x']⊢>τ' = bind-tl-xx Γ[x']⊢>τ'
... | yes x≡y | bind-hd | bind-tl-xy Γ[x']⊢>τ' x'≢y = bind-tl-xy Γ[x']⊢>τ' x'≢y
... | yes x≡y | bind-tl-xy _ x≢y | _ = ⊥-elim (x≢y x≡y)
... | no x≢y | bind-hd | _ = ⊥-elim (x≢y refl)
... | no x≢y | bind-tl-xy _ _ | bind-hd = bind-hd
... | no x≢y
    | bind-tl-xy Γ[x]⊢>τ _
    | bind-tl-xx {_} {_} {_} {_} {i'} Γ[x']⊢>τ' =
      bind-tl-xx
        (replace-spec-xy Γ name (N x' i') τ τ' Γ[x]⊢>τ Γ[x']⊢>τ' name≢pname')
      where
        -- We can use [x≢y] here because [bind-tl-xx] forces [x' ≡ y]
        name≢pname' : N x zero ≢ N x' i'
        name≢pname' Nx0≡Nx'i' = x≢y (extract-N-x-≡ Nx0≡Nx'i')
... | no x≢y | bind-tl-xy Γ[x]⊢>τ _ | bind-tl-xy Γ[x']⊢>τ' x'≢y =
        bind-tl-xy
          (replace-spec-xy Γ name name' τ τ' Γ[x]⊢>τ Γ[x']⊢>τ' name≢name')
          x'≢y
replace-spec-xy {T} {{TLift}}
    (E y ρ ∷ Γ)
    name@(N x (suc i))
    name'@(N x' i')
    τ τ'
    name∈Γ name'∈Γ
    name≢name'
  with x ≟ y | name∈Γ | name'∈Γ
... | yes x≡y | bind-tl-xx Γ[x]⊢>τ | bind-hd = bind-hd
... | yes x≡y
    | bind-tl-xx Γ[x]⊢>τ
    | bind-tl-xx {_} {_} {_} {_} {i'} Γ[x']⊢>τ' =
      bind-tl-xx
        (replace-spec-xy Γ (N x i) (N x' i') τ τ' Γ[x]⊢>τ Γ[x']⊢>τ' pname≢pname')
      where
        pname≢pname' : N x i ≢ N x' i'
        pname≢pname' Nxi≡Nx'i' =
          name≢name' (cong (N x ∘ suc) (extract-N-i-≡ Nxi≡Nx'i'))
... | yes x≡y | bind-tl-xx Γ[x]⊢>τ | bind-tl-xy Γ[x']⊢>τ' x'≢y =
      bind-tl-xy
        (replace-spec-xy Γ (N x i) name' τ τ' Γ[x]⊢>τ Γ[x']⊢>τ' pname≢name')
        x'≢y
      where
        pname≢name' : N x i ≢ N x' i'
        pname≢name' Nxi≡Nx'i' = x'≢y (extract-N-x-≡ (sym Nxi≡Nx'i'))
... | yes x≡y | bind-tl-xy _ x≢y | _  = ⊥-elim (x≢y x≡y)
... | no x≢y | bind-tl-xx _ | _ = ⊥-elim (x≢y refl)
... | no x≢y | bind-tl-xy Γ[x]⊢>τ _ | bind-hd = bind-hd
... | no x≢y
    | bind-tl-xy Γ[x]⊢>τ _
    | bind-tl-xx {_} {_} {_} {_} {i'} Γ[x']⊢>τ' =
      bind-tl-xx
        (replace-spec-xy Γ name (N x' i') τ τ' Γ[x]⊢>τ Γ[x']⊢>τ' name≢pname')
      where
        name≢pname' : N x (suc i) ≢ N x' i'
        name≢pname' Nx0≡Nx'i' = x≢y (extract-N-x-≡ Nx0≡Nx'i')
... | no x≢y | bind-tl-xy Γ[x]⊢>τ _ | bind-tl-xy Γ[x']⊢>τ' x'≢y =
      bind-tl-xy
        (replace-spec-xy Γ name name' τ τ' Γ[x]⊢>τ Γ[x']⊢>τ' name≢name')
        x'≢y
