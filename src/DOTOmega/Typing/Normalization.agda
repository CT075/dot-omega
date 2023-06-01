open import Level renaming (zero to lzero; suc to lsuc) hiding (Lift)
open import Relation.Binary using (DecSetoid)

module DOTOmega.Typing.Normalization
    (TypeL : DecSetoid lzero lzero)
    (TermL : DecSetoid lzero lzero)
  where

open import Data.List using (List; [])
open import Data.String using (String)

open import Data.Nat.Properties using (<-trans)
open import Data.Sum
open import Data.Product
open import Data.Empty renaming (⊥ to Void)
open import Relation.Binary.PropositionalEquality hiding (J)
open import Induction
open import Induction.WellFounded
open import Induction.Extensions

open import DOTOmega.Syntax TypeL TermL
open import DOTOmega.Typing TypeL TermL
open import DOTOmega.Typing.Tight TypeL TermL
open import DOTOmega.Typing.Tight.Properties TypeL TermL

open import Data.Var
open import Data.Context

infix 4 _whnf

data _whnf : Type → Set where
  ⊤-whnf : ⊤ whnf
  ⊥-whnf : ⊥ whnf
  ℿ-whnf : ∀{S T} → ℿ S T whnf
  ƛ-whnf : ∀{K A} → ƛ K A whnf
  ∧-whnf : ∀{S U} → S whnf → U whnf → S ∧ U whnf
  μ-whnf : ∀{A} → μ A whnf
  typdecl-whnf : ∀{K M} → [ typ M ∶ K ] whnf
  valdecl-whnf : ∀{ℓ A} → [ val ℓ ∶ A ] whnf

lift-preserves-whnf : ∀ f A → A whnf → liftType f A whnf
lift-preserves-whnf f ⊤ ⊤-whnf = ⊤-whnf
lift-preserves-whnf f ⊥ ⊥-whnf = ⊥-whnf
lift-preserves-whnf f [ typ M ∶ K ] typdecl-whnf = typdecl-whnf
lift-preserves-whnf f [ val ℓ ∶ A ] valdecl-whnf = valdecl-whnf
lift-preserves-whnf f (A ∧ B) (∧-whnf A-whnf B-whnf) =
  ∧-whnf (lift-preserves-whnf f A A-whnf) (lift-preserves-whnf f B B-whnf)
lift-preserves-whnf f (μ A) μ-whnf = μ-whnf
lift-preserves-whnf f (ℿ J K) ℿ-whnf = ℿ-whnf
lift-preserves-whnf f (ƛ x A) ƛ-whnf = ƛ-whnf

infix 4 _tyval _store

data _tyval : Kind → Set where
  intv-val : ∀ {α} → α whnf → α ∙∙ α tyval
  pi-val : ∀ {J K} → K inert-kd → ℿ J K tyval

data _store : Context → Set where
  empty-store : [] store
  cons-store-kd : ∀ {Γ x k} → Γ store → k tyval → Γ & x ~ Kd k store
  cons-store-ty : ∀ {Γ x τ} → Γ store → τ inert-ty → Γ & x ~ Ty τ store

denot : Context → Type → (K : Kind) → (s : KindShape) → Set
denot Γ τ (S ∙∙ U) _ = τ whnf × Γ ⊢#ty S ≤ τ ∈ ✶ × Γ ⊢#ty τ ≤ U ∈ ✶
denot Γ (ƛ J' A) (ℿ J K) (Pi sJ sK) =
    Γ ⊢#kd J ≤ J' ×
    (∀ τ x →
      denot Γ τ J sJ →
      Γ & x ~ Kd S[ τ ∈ J ] ⊢#ty openType x A ∈ openKind x K →
      Σ[ α ∈ Type ]
      ((Γ & x ~ Kd S[ τ ∈ J ]) ⊢#ty A == α ∈ openKind x K ×
        denot (Γ & x ~ Kd S[ τ ∈ J ]) α (openKind x K) sK))
denot Γ _ (ℿ J K) _ = Void

⟨_,_⟩∈'⟦_⟧ : Context → Type → Kind → Set
⟨ Γ , A ⟩∈'⟦ K ⟧ = denot Γ A K (kd-shape K)

mutual
  data ⟨_,_⟩∈⟦_⟧ : Context → Type → Kind → Set where
    denot-intv : ∀{Γ τ S U} →
      τ whnf → Γ ⊢#ty S ≤ τ ∈ ✶ → Γ ⊢#ty τ ≤ U ∈ ✶ → ⟨ Γ , τ ⟩∈⟦ S ∙∙ U ⟧
    denot-pi : ∀{Γ J' A J K} →
      Γ ⊢#kd J ≤ J' →
      (∀ τ x →
        ⟨ Γ , τ ⟩∈'⟦ J ⟧ →
        Γ & x ~ Kd S[ τ ∈ J ] ⊢#ty openType x A ∈ openKind x K →
        ⟨ Γ & x ~ Kd S[ τ ∈ J ] , A ⟩∈ℰ⟦ openKind x K ⟧) →
      ⟨ Γ , ƛ J' A ⟩∈⟦ ℿ J K ⟧

  data ⟨_,_⟩∈ℰ⟦_⟧ : Context → Type → Kind → Set where
    denot-eval : ∀{Γ A K} τ →
      Γ ⊢#ty A == τ ∈ K →
      ⟨ Γ , τ ⟩∈⟦ K ⟧ →
      ⟨ Γ , A ⟩∈ℰ⟦ K ⟧

