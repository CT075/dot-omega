module Induction.Extensions where

open import Level
open import Data.Nat using (ℕ; _<_; zero; suc; s≤s)
open import Data.Nat.Properties using (n≮0; <-trans)
open import Data.Nat.Induction using (<-recBuilder)
open import Data.Product
open import Data.Sum
open import Data.Empty using (⊥-elim)
open import Induction
open import Induction.WellFounded
open import Induction.Lexicographic
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding (trans; [_])

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

-- [Induction.Lexicographic] is completely inscrutable, so this helper is
-- easier to use.
-- TODO: make this dependent
<-lex : ∀{ℓ}
  {A : Set ℓ} {B : Set ℓ} →
  (_<A_ : Rel A ℓ) →
  (_<B_ : Rel B ℓ) →
  A × B → A × B → Set ℓ
<-lex _<A_ _<B_ (a₁ , b₁) (a₂ , b₂) = a₁ <A a₂ ⊎ (a₁ ≡ a₂ × b₁ <B b₂)

<-lex-wf : ∀{ℓ} {A : Set ℓ} {B : Set ℓ} {_<A_ : Rel A ℓ} {_<B_ : Rel B ℓ} →
  WellFounded _<A_ → WellFounded _<B_ →
  WellFounded (<-lex _<A_ _<B_)
<-lex-wf {ℓ} {A} {B} {_<A_} {_<B_} <A-wf <B-wf t =
    build [ <A-recBuilder ⊗ <B-recBuilder ] (Acc _<A×B_) go t
  where
    _<A×B_ = <-lex _<A_ _<B_

    open All <A-wf ℓ
      renaming (wfRecBuilder to <A-recBuilder)
      hiding (wfRec-builder)
    open All <B-wf ℓ
      renaming (wfRecBuilder to <B-recBuilder)
      hiding (wfRec-builder)

    go : ∀ t →
      ((∀ b → b <B proj₂ t → Acc _<A×B_ (proj₁ t , b)) ×
       (∀ a → a <A proj₁ t → ∀ b' → Acc _<A×B_ (a , b'))) →
      Acc _<A×B_ t
    go t@(a , b) (B-rec , A-rec) = acc recurse
      where
        recurse : ∀ t' → t' <A×B t → Acc _<A×B_ t'
        recurse (a' , b') (inj₁ a'<a) = A-rec a' a'<a b'
        recurse (a' , b') (inj₂ (a'≡a , b'<b)) rewrite a'≡a = B-rec b' b'<b

