module Data.Nat.Induction.Extensions where

open import Data.Nat using (ℕ; _<_; zero; suc; s≤s)
open import Data.Nat.Properties using (n≮0; <-trans)
open import Data.Nat.Induction using (<-recBuilder)
open import Data.Empty using (⊥-elim)
open import Induction
open import Induction.WellFounded
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding (trans)

withMeasure : ∀ {α} {β} {T : Set α} →
  (measure : T → ℕ) →
  (P : T → Set β) →
  (∀ x → (∀ y → measure y < measure x → P y) → P x) →
  (x : T) →
  P x
withMeasure measure P f x = build <-recBuilder
    (λ measureX → (∀ x → (measure x ≡ measureX) → P x))
    f'
    (measure x)
    x
    refl
  where
    f' : ∀ measureX →
        (∀ measureY → measureY < measureX → ∀ y → (measure y ≡ measureY) → P y) →
        ∀ x → (measure x ≡ measureX) → P x
    f' measureX rec x mx≡measureX = f x rec'
      where
        rec' : ∀ y → measure y < measure x → P y
        rec' y my<mx rewrite mx≡measureX = rec (measure y) my<mx y refl

accMeasure : ∀ {ℓ} {T : Set ℓ} →
  (measure : T → ℕ) →
  (x : T) →
  Acc (λ a b → measure a < measure b) x
accMeasure {ℓ} {T} measure x = withMeasure measure (Acc _<t_) go x
  where
    _<t_ : T → T → Set
    a <t b = measure a < measure b

    go : ∀ x → (∀ y → measure y < measure x → Acc _<t_ y) → Acc _<t_ x
    go x rec = acc rec
