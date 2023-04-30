open import Level renaming (zero to lzero; suc to lsuc) hiding (Lift)
open import Relation.Binary using (DecSetoid)

module DOTOmega.Typing.Normalization
    (TypeL : DecSetoid lzero lzero)
    (TermL : DecSetoid lzero lzero)
  where

open import Data.Nat.Properties using (<-trans)
open import Data.Product
open import Data.Empty renaming (⊥ to Void)
open import Relation.Binary.PropositionalEquality hiding (J)
open import Induction.WellFounded using (Acc; acc)

open import DOTOmega.Syntax TypeL TermL
open import DOTOmega.Typing TypeL TermL
open import DOTOmega.Typing.Tight TypeL TermL
open import DOTOmega.Typing.Tight.Properties TypeL TermL

open import Data.Context

infix 4 _normal

data _normal : Type → Set where
  ⊤-norm : ⊤ normal
  ⊥-norm : ⊥ normal
  ℿ-norm : ∀{τ e} → ƛ τ e normal
  ƛ-norm : ∀{K A} → ƛ K A normal
  ∧-norm : ∀{S U} → S normal → U normal → S ∧ U normal
  μ-norm : ∀{A} → μ A normal
  typdecl-norm : ∀{K M} → [ typ M ∶ K ] normal
  valdecl-norm : ∀{ℓ A} → A normal → [ val ℓ ∶ A ] normal

{-
mutual
  data ⟨_,_⟩∈⟦_⟧ : Context → Type → Kind → Set where
    denot-intv : ∀{Γ τ S U} →
      τ normal →
      Γ ⊢#ty S ≤ τ ∈ ✶ →
      Γ ⊢#ty τ ≤ U ∈ ✶ →
      ⟨ Γ , τ ⟩∈⟦ S ∙∙ U ⟧
    denot-abs : ∀{Γ x} {J J' : Kind} {K : Kind} {A} →
      Γ ⊢#kd J ≤ J' →
      (∀ τ → ⟨ Γ , τ ⟩∈⟦ J ⟧ → ⟨ Γ & x ~ Kd S[ τ ∈ J ] , A ⟩∈ℰ⟦ openKind x K ⟧) →
      ⟨ Γ , ƛ J' A ⟩∈⟦ ℿ J K ⟧

  data ⟨_,_⟩∈ℰ⟦_⟧ : Context → Type → Kind → Set where
    eval : ∀{Γ A τ K} → Γ ⊢#ty A == τ ∈ K → ⟨ Γ , τ ⟩∈⟦ K ⟧ → ⟨ Γ , A ⟩∈ℰ⟦ K ⟧
-}

data LRSort : Set where
  ValS : LRSort
  EvalS : LRSort

data _<lr_ : LRSort → LRSort → Set where
  ValS<EvalS : ValS <lr EvalS

lr-acc : ∀ t → Acc _<lr_ t
lr-acc ValS = acc (λ _ ())
lr-acc EvalS = acc (λ where ValS _ → acc (λ _ ()))

-- TODO: oh god
{-# TERMINATING #-}
denot : LRSort → Context → Type → Kind → Set
denot ValS Γ τ (S ∙∙ U) =
  τ normal ×
  Γ ⊢#ty S ≤ τ ∈ ✶ ×
  Γ ⊢#ty τ ≤ U ∈ ✶
denot ValS Γ (ƛ J' A) (ℿ J K) =
    Γ ⊢#kd J ≤ J' ×
    (∀ τ x →
      denot ValS Γ τ J →
      denot EvalS (Γ & x ~ Kd S[ τ ∈ J ]) A (openKind x K))
denot ValS _ _ (ℿ J K) = Void
denot EvalS Γ A K = Σ[ τ ∈ Type ](Γ ⊢#ty A == τ ∈ K × denot ValS Γ τ K)

-- TODO: need to include [LRSort] somehow
denot-step : LRSort → Context → Type → (K : Kind) → Acc _<kd_ K → Set
denot-step ValS Γ τ (S ∙∙ U) (acc rec) =
  τ normal ×
  Γ ⊢#ty S ≤ τ ∈ ✶ ×
  Γ ⊢#ty τ ≤ U ∈ ✶
denot-step ValS Γ (ƛ J' A) (ℿ J K) (acc rec) =
    Γ ⊢#kd J ≤ J' ×
    (∀ τ x →
      denot-step ValS Γ τ J (rec _ (<kd-ℿ₁ J K)) →
      denot-step EvalS (Γ & x ~ Kd S[ τ ∈ J ]) A (openKind x K)
        (rec _ (<kd-ℿ-open x J K)))
denot-step ValS _ _ (ℿ J K) (acc rec) = Void
denot-step EvalS Γ A K (acc rec) =
  Σ[ τ ∈ Type ](
    Γ ⊢#ty A == τ ∈ K ×
    (denot-step ValS Γ τ K {!!}))

⟨_,_⟩∈'⟦_⟧ : Context → Type → Kind → Set
⟨ Γ , τ ⟩∈'⟦ K ⟧ = denot ValS Γ τ K

⟨_,_⟩∈'ℰ⟦_⟧ : Context → Type → Kind → Set
⟨ Γ , τ ⟩∈'ℰ⟦ K ⟧ = denot EvalS Γ τ K

