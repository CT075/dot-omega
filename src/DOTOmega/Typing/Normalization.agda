open import Level renaming (zero to lzero; suc to lsuc) hiding (Lift)
open import Relation.Binary using (DecSetoid)

module DOTOmega.Typing.Normalization
    (TypeL : DecSetoid lzero lzero)
    (TermL : DecSetoid lzero lzero)
  where

open import Data.List using (List)
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

denot : Context → Type → (K : Kind) → (s : KindShape) → Set
denot Γ τ (S ∙∙ U) _ = τ normal × Γ ⊢#ty S ≤ τ ∈ ✶ × Γ ⊢#ty τ ≤ U ∈ ✶
denot Γ (ƛ J' A) (ℿ J K) (Pi sJ sK) =
    Γ ⊢#kd J ≤ J' ×
    (∀ τ x →
      denot Γ τ J sJ →
      Σ[ α ∈ Type ]
      ((Γ & x ~ Kd S[ τ ∈ J ]) ⊢#ty A == α ∈ openKind x K ×
        denot (Γ & x ~ Kd S[ τ ∈ J ]) α (openKind x K) sK))
denot Γ _ (ℿ J K) _ = Void

⟨_,_⟩∈⟦_⟧ : Context → Type → Kind → Set
⟨ Γ , τ ⟩∈⟦ K ⟧ = denot Γ τ K (kd-shape K)

⟨_,_⟩∈ℰ⟦_⟧ : Context → Type → Kind → Set
⟨ Γ , A ⟩∈ℰ⟦ K ⟧ =
  Σ[ τ ∈ Type ](Γ ⊢#ty A == τ ∈ K × denot Γ τ K (kd-shape K))

prop-open : ∀ {Γ τ} x K →
  denot Γ τ (openKind x K) (kd-shape K) ≡
  denot Γ τ (openKind x K) (kd-shape (openKind x K))
prop-open x K rewrite liftKind-preserves-shape (openVar x) K = refl

conv-open : ∀ {Γ τ} x K →
  denot Γ τ (openKind x K) (kd-shape K) →
  denot Γ τ (openKind x K) (kd-shape (openKind x K))
conv-open {Γ} {τ} x K p rewrite prop-open {Γ} {τ} x K = p

mutual
  data ⟨_,_⟩∈'⟦_⟧ : Context → Type → Kind → Set where
    denot-intv : ∀ {Γ τ S U} →
      τ normal →
      Γ ⊢#ty S ≤ τ ∈ ✶ → Γ ⊢#ty τ ≤ U ∈ ✶ →
      ⟨ Γ , τ ⟩∈'⟦ S ∙∙ U ⟧
    denot-abs : ∀ {Γ J J' A K} →
      Γ ⊢#kd J ≤ J' →
      (∀ τ x →
        ⟨ Γ , τ ⟩∈⟦ J ⟧ →
        ⟨ Γ & x ~ Kd S[ τ ∈ J ] , A ⟩∈'ℰ⟦ openKind x K ⟧) →
      ⟨ Γ , ƛ J' A ⟩∈'⟦ ℿ J K ⟧

  data ⟨_,_⟩∈'ℰ⟦_⟧ (Γ : Context) (A : Type) (K : Kind) : Set where
    eval : ∀ τ → Γ ⊢#ty A == τ ∈ K → ⟨ Γ , τ ⟩∈'⟦ K ⟧ →
      ⟨ Γ , A ⟩∈'ℰ⟦ K ⟧

mutual
  denot-rec-ind-v : ∀ {Γ τ K} → ⟨ Γ , τ ⟩∈⟦ K ⟧ → ⟨ Γ , τ ⟩∈'⟦ K ⟧
  denot-rec-ind-v {K = S ∙∙ U} (τ-normal , S≤τ , τ≤U) =
    denot-intv τ-normal S≤τ τ≤U
  denot-rec-ind-v {Γ} {ƛ J' A} {ℿ J K} (J≤J' , f) = denot-abs J≤J' f'
    where
      f' : ∀ τ x →
        ⟨ Γ , τ ⟩∈⟦ J ⟧ →
        ⟨ Γ & x ~ Kd S[ τ ∈ J ] , A ⟩∈'ℰ⟦ openKind x K ⟧
      f' τ x ⟨Γ,τ⟩∈⟦J⟧ = foo
        where
          t = f τ x ⟨Γ,τ⟩∈⟦J⟧
          α = proj₁ t
          A==α = proj₁ (proj₂ t)

          ⟨Γx,α⟩∈⟦xK⟧ : denot _ α (openKind x K) (kd-shape K)
          ⟨Γx,α⟩∈⟦xK⟧ = proj₂ (proj₂ t)

          foo = denot-rec-ind-e (α , A==α , conv-open x K ⟨Γx,α⟩∈⟦xK⟧)

  denot-rec-ind-e : ∀ {Γ A K} → ⟨ Γ , A ⟩∈ℰ⟦ K ⟧ → ⟨ Γ , A ⟩∈'ℰ⟦ K ⟧
  denot-rec-ind-e (τ , A==τ , ⟨Γ,τ⟩∈⟦K⟧) = eval τ A==τ (denot-rec-ind-v ⟨Γ,τ⟩∈⟦K⟧)

{-
strong-normalization : ∀ {Γ A K} → Γ inert-ctx → Γ ⊢#ty A ∈ K → ⟨ Γ , A ⟩∈ℰ⟦ K ⟧
strong-normalization Γinert (k-var-# Γctx Γ[x]⊢>K) = {! !}
strong-normalization Γinert k-top-# =
  (⊤ , ty-refl k-top-# , ⊤-norm , st-bot-# k-top-# , st-top-# k-top-#)
strong-normalization Γinert k-bot-# =
  (⊥ , ty-refl k-bot-# , ⊥-norm , st-bot-# k-bot-# , st-top-# k-bot-#)
strong-normalization Γinert (k-sing-# Γ⊢#A∈S∙∙U) =
  let (τ , Γ⊢#tyA==τ , τ-norm , S≤τ , τ≤U) = strong-normalization Γinert Γ⊢#A∈S∙∙U
   in
  (τ , {!!} , τ-norm , {!!} , {!!})
strong-normalization Γinert (k-arr-# Γ⊢#A∈✶ Γx∶A⊢#B∈✶) = {! !}
strong-normalization Γinert (k-abs-# Γ⊢#J-kd Γx∶J⊢#K-kd) = {! !}
strong-normalization {Γ} Γinert (k-app-# {J} {K} Γ⊢#f∈ℿJK Γ⊢#B∈J) =
  let (ƛJ'A , Γ⊢#f==ƛJ'A , ⟨Γ,ƛJ'A⟩∈⟦ℿJK⟧) = strong-normalization Γinert Γ⊢#f∈ℿJK
      (τ , Γ⊢#B==τ , ⟨Γ,τ⟩∈⟦J⟧) = strong-normalization Γinert Γ⊢#B∈J
      (J' , A) = unwrap ƛJ'A ⟨Γ,ƛJ'A⟩∈⟦ℿJK⟧
   in
  {!!}
  where
    unwrap : (B : Type) → ⟨ Γ , B ⟩∈⟦ ℿ J K ⟧ →
      Σ[ (J' , A) ∈ Kind × Type ](
        Γ ⊢#kd J ≤ J' ×
        (∀ τ x → ⟨ Γ , τ ⟩∈⟦ J ⟧ → ⟨ Γ & x ~ Kd S[ τ ∈ J ] , A ⟩∈ℰ⟦ openKind x K ⟧))
    unwrap (ƛ J' A) (J≤J' , f) = (J' , A) , J≤J' , {! f !}
    -- This extra case is necessary to convince the typechecker that all other
    -- cases are impossible
    unwrap ⊤ ()
strong-normalization Γinert (k-intersect-# Γ⊢#τ₁∈S₁∙∙U₁ Γ⊢#τ₂∈S₂∙∙U₂) = {! !}
strong-normalization Γinert (k-sub-# Γ⊢#A∈J Γ⊢#J≤K) = {! !}
strong-normalization Γinert (k-field-# Γ⊢#τ∈S∙∙U) = {! !}
strong-normalization Γinert (k-typ-# Γ⊢#K-kd) = {! !}
strong-normalization Γinert (k-sel-# Γ⊢!x∈U⟫[typ-A∶S[τ∈K]]) = {! !}
-}
