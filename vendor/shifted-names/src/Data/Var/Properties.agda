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
open-close-id x (Free (N y zero)) = begin
    open' x (close x (Free (N y zero)))
  ≡⟨ refl ⟩
    open' x (lower Free (Bound zero) x (N y zero))
  ≡⟨ refl ⟩
    open' x (if x == y then Bound zero else Free (N y zero))
  ≡⟨ push-function-into-if (open' x) (x == y) {Bound zero} {Free (N y zero)} ⟩
    (if x == y then open' x (Bound zero) else open' x (Free (N y zero)))
  ≡⟨ refl ⟩
    (if x == y then Free (N x zero) else Free (bump x (N y zero)))
  ≡⟨ refl ⟩
    (if x == y then Free (N x zero) else Free (if x == y then N y (suc zero) else N y zero))
  ≡⟨ cong
       (λ t → if x == y then Free (N x zero) else t)
       (push-function-into-if Free (x == y) {N y (suc zero)} {N y zero})
   ⟩
    (if x == y then Free (N x zero) else (if x == y then Free (N y (suc zero)) else Free (N y zero)))
  ≡⟨ nested-if-same-cond-else (x == y) (Free (N x zero)) (Free (N y zero)) ⟩
    (if x == y then Free (N x zero) else Free (N y zero))
  ≡⟨ if-else-subst x y (λ x → Free (N x zero)) (Free (N y zero)) ⟩
    (if x == y then Free (N y zero) else Free (N y zero))
  ≡⟨ if-both-branches (x == y) (Free (N y zero)) ⟩
    Free (N y zero)
  ∎
open-close-id x (Free (N y (suc i))) = begin
    open' x (close x (Free (N y (suc i))))
  ≡⟨ refl ⟩
    open' x (if x == y then Free (N y i) else Free (N y (suc i)))
  ≡⟨ push-function-into-if (open' x) (x == y) {Free (N y i)} {Free (N y (suc i))} ⟩
    (if x == y then open' x (Free (N y i)) else open' x (Free (N y (suc i))))
  ≡⟨ refl ⟩
    (if x == y then
      Free (if x == y then (N y (suc i)) else (N y i))
    else
      open' x (Free (N y (suc i))))
  ≡⟨ cong
       (λ t → if x == y then t else open' x (Free (N y (suc i))))
       (push-function-into-if Free (x == y) {N y (suc i)} {N y i})
   ⟩
    (if x == y then
      (if x == y then Free (N y (suc i)) else Free (N y i))
    else
      open' x (Free (N y (suc i))))
  ≡⟨ refl ⟩
    (if x == y then
      (if x == y then Free (N y (suc i)) else Free (N y i))
    else
      Free (if x == y then N y (suc (suc i)) else N y (suc i)))
  ≡⟨ cong
       (λ t → if x == y then (if x == y then Free (N y (suc i)) else Free (N y i)) else t)
       (push-function-into-if Free (x == y) {N y (suc (suc i))} {N y (suc i)})
   ⟩
    (if x == y then
      (if x == y then Free (N y (suc i)) else Free (N y i))
    else
      (if x == y then Free (N y (suc (suc i))) else Free (N y (suc i))))
  ≡⟨ nested-if-same-cond-if (x == y)
       (Free (N y (suc i)))
       (if x == y then Free (N y (suc (suc i))) else Free (N y (suc i))) ⟩
    (if x == y then Free (N y (suc i)) else
      (if x == y then Free (N y (suc (suc i))) else Free (N y (suc i))))
  ≡⟨ nested-if-same-cond-else (x == y) (Free (N y (suc i))) (Free (N y (suc i))) ⟩
    (if x == y then Free (N y (suc i)) else Free (N y (suc i)))
  ≡⟨ if-both-branches (x == y) (Free (N y (suc i))) ⟩
    Free (N y (suc i))
  ∎

close-open-id : ∀ x v → close x (open' x v) ≡ v
close-open-id x (Bound zero) = begin
    close x (open' x (Bound zero))
  ≡⟨ refl ⟩
    close x (Free (N x zero))
  ≡⟨ refl ⟩
    (if x == x then Bound zero else Free (N x zero))
  ≡⟨ cong (λ c → if c then Bound zero else Free (N x zero)) (==-refl x) ⟩
    (if true then Bound zero else Free (N x zero))
  ≡⟨ refl ⟩
    Bound zero
  ∎
close-open-id x (Bound (suc n)) = refl
close-open-id x (Free (N y zero)) = begin
    close x (open' x (Free (N y zero)))
  ≡⟨ refl ⟩
    close x (Free (if x == y then N y (suc zero) else N y zero))
  ≡⟨ push-function-into-if (λ t → (close x (Free t))) (x == y) ⟩
    (if x == y then close x (Free (N y (suc zero))) else close x (Free (N y zero)))
  ≡⟨ refl ⟩
    (if x == y then
      (if x == y then Free (N y zero) else Free (N y (suc zero)))
    else
      (if x == y then Bound zero else Free (N y zero)))
  ≡⟨ nested-if-same-cond-if (x == y)
       (Free (N y zero))
       (if x == y then Bound zero else Free (N y zero)) ⟩
    (if x == y then Free (N y zero) else
      (if x == y then Bound zero else Free (N y zero)))
  ≡⟨ nested-if-same-cond-else (x == y) (Free (N y zero)) (Free (N y zero)) ⟩
    (if x == y then Free (N y zero) else Free (N y zero))
  ≡⟨ if-both-branches (x == y) (Free (N y zero)) ⟩
    Free (N y zero)
  ∎
close-open-id x (Free (N y (suc i))) = begin
    close x (open' x (Free (N y (suc i))))
  ≡⟨ refl ⟩
    close x (Free (if x == y then N y (suc (suc i)) else N y (suc i)))
  ≡⟨ push-function-into-if (λ t → (close x (Free t))) (x == y) ⟩
    (if x == y then close x (Free (N y (suc (suc i)))) else close x (Free (N y (suc i))))
  ≡⟨ refl ⟩
    (if x == y then
      (if x == y then Free (N y (suc i)) else Free (N y (suc (suc i))))
    else
      (if x == y then Free (N y i) else Free (N y (suc i))))
  ≡⟨ nested-if-same-cond-if (x == y)
       (Free (N y (suc i)))
       (if x == y then Free (N y i) else Free (N y (suc i))) ⟩
    (if x == y then Free (N y (suc i)) else
      (if x == y then Free (N y i) else Free (N y (suc i))))
  ≡⟨ nested-if-same-cond-else (x == y) (Free (N y (suc i))) (Free (N y (suc i))) ⟩
    (if x == y then Free (N y (suc i)) else Free (N y (suc i)))
  ≡⟨ if-both-branches (x == y) (Free (N y (suc i))) ⟩
    Free (N y (suc i))
  ∎

module _ {ℓ} (T : Set ℓ) (Ops : MakeOps T) where
  open MakeOps Ops

  bind-wk-id : ∀ u v → bind u (wk v) ≡ var v
  bind-wk-id u (Bound n) = refl
  bind-wk-id u (Free name) = refl
