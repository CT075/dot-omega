module Data.Var.Properties where

open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero)
open import Data.String using (String; _==_; _≟_)
open import Data.String.Properties using (≈⇒≡; ≈-refl)
open import Data.Bool using (if_then_else_; true; false)
open import Data.Bool.Properties using (push-function-into-if)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality as PropEq
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (map′; isYes)

open import Data.Var.Base

open ≡-Reasoning

==-refl : ∀ (x : String) → (x == x) ≡ true
==-refl x with x ≟ x
... | yes p = refl
... | no ¬p = ⊥-elim (¬p refl)

if-both-branches : ∀ {a : Set} c (t : a) → (if c then t else t) ≡ t
if-both-branches true t = refl
if-both-branches false t = refl

if-else-subst : ∀{a : Set} x y (f : String → a) (t : a) →
    (if x == y then f x else t)
  ≡ (if x == y then f y else t)
if-else-subst x y f t with x ≟ y
... | yes p rewrite p = refl
... | no ¬p = refl

nested-if-same-cond-if : ∀ {a : Set} c (t1 : a) {t2} t3 →
    (if c then (if c then t1 else t2) else t3)
  ≡ (if c then t1 else t3)
nested-if-same-cond-if true t1 {t2} t3 = refl
nested-if-same-cond-if false t1 {t2} t3 = refl

nested-if-same-cond-else : ∀ {a : Set} c (t1 : a) {t2} t3 →
    (if c then t1 else (if c then t2 else t3))
  ≡ (if c then t1 else t3)
nested-if-same-cond-else true t1 {t2} t3 = refl
nested-if-same-cond-else false t1 {t2} t3 = refl

open-close-id : ∀ x v → open' x (close x v) ≡ v
open-close-id x (Bound n) = refl
open-close-id x (Free y zero) = begin
    open' x (close x (Free y zero))
  ≡⟨ refl ⟩
    open' x (if x == y then Bound zero else Free y zero)
  ≡⟨ push-function-into-if (open' x) (x == y) {Bound zero} {Free y zero} ⟩
    (if x == y then open' x (Bound zero) else open' x (Free y zero))
  ≡⟨ refl ⟩
    (if x == y then Free x zero else (if x == y then Free y (suc zero) else Free y zero))
  ≡⟨ nested-if-same-cond-else (x == y) (Free x zero) (Free y zero) ⟩
    (if x == y then Free x zero else Free y zero)
  ≡⟨ if-else-subst x y (λ x → Free x zero) (Free y zero) ⟩
    (if x == y then Free y zero else Free y zero)
  ≡⟨ if-both-branches (x == y) (Free y zero) ⟩
    Free y zero
  ∎
open-close-id x (Free y (suc i)) = begin
    open' x (close x (Free y (suc i)))
  ≡⟨ refl ⟩
    open' x (if x == y then Free y i else Free y (suc i))
  ≡⟨ push-function-into-if (open' x) (x == y) {Free y i} {Free y (suc i)} ⟩
    (if x == y then open' x (Free y i) else open' x (Free y (suc i)))
  ≡⟨ refl ⟩
    (if x == y then
      (if x == y then Free y (suc i) else Free y i)
    else
      (if x == y then Free y (suc (suc i)) else Free y (suc i)))
  ≡⟨ nested-if-same-cond-if (x == y)
       (Free y (suc i))
       (if x == y then Free y (suc (suc i)) else Free y (suc i)) ⟩
    (if x == y then Free y (suc i) else
      (if x == y then Free y (suc (suc i)) else Free y (suc i)))
  ≡⟨ nested-if-same-cond-else (x == y) (Free y (suc i)) (Free y (suc i)) ⟩
    (if x == y then Free y (suc i) else Free y (suc i))
  ≡⟨ if-both-branches (x == y) (Free y (suc i)) ⟩
    Free y (suc i)
  ∎

close-open-id : ∀ x v → close x (open' x v) ≡ v
close-open-id x (Bound zero) = begin
    close x (open' x (Bound zero))
  ≡⟨ refl ⟩
    close x (Free x zero)
  ≡⟨ refl ⟩
    (if x == x then Bound zero else Free x zero)
  ≡⟨ cong (λ c → if c then Bound zero else Free x zero) (==-refl x) ⟩
    (if true then Bound zero else Free x zero)
  ≡⟨ refl ⟩
    Bound zero
  ∎
close-open-id x (Bound (suc n)) = refl
close-open-id x (Free y zero) = begin
    close x (open' x (Free y zero))
  ≡⟨ refl ⟩
    close x (if x == y then Free y (suc zero) else Free y zero)
  ≡⟨ push-function-into-if (close x) (x == y) ⟩
    (if x == y then close x (Free y (suc zero)) else close x (Free y zero))
  ≡⟨ refl ⟩
    (if x == y then
      (if x == y then Free y zero else Free y (suc zero))
    else
      (if x == y then Bound zero else Free y zero))
  ≡⟨ nested-if-same-cond-if (x == y)
       (Free y zero)
       (if x == y then Bound zero else Free y zero) ⟩
    (if x == y then Free y zero else
      (if x == y then Bound zero else Free y zero))
  ≡⟨ nested-if-same-cond-else (x == y) (Free y zero) (Free y zero) ⟩
    (if x == y then Free y zero else Free y zero)
  ≡⟨ if-both-branches (x == y) (Free y zero) ⟩
    Free y zero
  ∎
close-open-id x (Free y (suc i)) = begin
    close x (open' x (Free y (suc i)))
  ≡⟨ refl ⟩
    close x (if x == y then Free y (suc (suc i)) else Free y (suc i))
  ≡⟨ push-function-into-if (close x) (x == y) ⟩
    (if x == y then close x (Free y (suc (suc i))) else close x (Free y (suc i)))
  ≡⟨ refl ⟩
    (if x == y then
      (if x == y then Free y (suc i) else Free y (suc (suc i)))
    else
      (if x == y then Free y i else Free y (suc i)))
  ≡⟨ nested-if-same-cond-if (x == y)
       (Free y (suc i))
       (if x == y then Free y i else Free y (suc i)) ⟩
    (if x == y then Free y (suc i) else
      (if x == y then Free y i else Free y (suc i)))
  ≡⟨ nested-if-same-cond-else (x == y) (Free y (suc i)) (Free y (suc i)) ⟩
    (if x == y then Free y (suc i) else Free y (suc i))
  ≡⟨ if-both-branches (x == y) (Free y (suc i)) ⟩
    Free y (suc i)
  ∎

module _ {ℓ} (T : Set ℓ) (Ops : MakeOps T) where
  open MakeOps Ops

  bind-wk-id : ∀ u v → bind u (wk v) ≡ var v
  bind-wk-id u (Bound n) = refl
  bind-wk-id u (Free x i) = refl
