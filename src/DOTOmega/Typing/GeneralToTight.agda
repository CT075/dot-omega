open import Level using () renaming (zero to lzero; suc to lsuc)
open import Relation.Binary using (DecSetoid)

module DOTOmega.Typing.GeneralToTight
    (TypeL : DecSetoid lzero lzero)
    (TermL : DecSetoid lzero lzero)
  where

open import Data.Nat using (ℕ; suc; _⊔_; s≤s) renaming (_<_ to _<ℕ_)
open import Data.Nat.Properties using (≤-reflexive; ≤-trans; m≤m⊔n; m≤n⊔m)
open import Data.Nat.Induction.Extensions
open import Data.Product
open import Data.List hiding ([_])
open import Relation.Binary.PropositionalEquality hiding (J)
open import Induction.WellFounded using (Acc; acc)

open import Data.Context
open import Data.Var

open import DOTOmega.Syntax TypeL TermL
open import DOTOmega.Typing TypeL TermL
open import DOTOmega.Typing.Properties TypeL TermL
open import DOTOmega.Typing.Tight TypeL TermL
open import DOTOmega.Typing.Tight.Properties TypeL TermL
open import DOTOmega.Typing.Precise TypeL TermL
open import DOTOmega.Typing.Precise.Properties TypeL TermL
open import DOTOmega.Typing.Invertible TypeL TermL
open import DOTOmega.Typing.Invertible.Properties TypeL TermL

postulate
  -- This is clearly true, but at the moment, [Γ & x ~ T] is defined as a
  -- function performing some computation (as opposed to a constructor),
  -- which Agda can have trouble with unifying.
  unwrap-inert-ctx : ∀ {Γ x fact} → (Γ & x ~ fact) inert-ctx → Γ inert-ctx

  sing-incl : ∀ {Γ J τ K} → J ≡ S[ τ ∈ K ] → Γ ⊢ J kd → Γ ⊢ty τ ∈ S[ τ ∈ K ]

sing-inv-∙∙ : ∀ τ K {S U} → S[ τ ∈ K ] ≡ S ∙∙ U →
  Σ[ p ∈ Type × Type ] (K ≡ proj₁ p ∙∙ proj₂ p)
sing-inv-∙∙ τ (S ∙∙ U) eq = ((S , U), refl)

un-∙∙ : ∀ {A B C D} → A ∙∙ B ≡ C ∙∙ D → A ≡ C
un-∙∙ refl = refl

sing-incl-# : ∀ {Γ J τ K} → J ≡ S[ τ ∈ K ] → Γ ⊢# J kd → Γ ⊢#ty τ ∈ S[ τ ∈ K ]
sing-incl-# {τ = τ} {K = K@(B ∙∙ C)} eq (wf-intv-# Γ⊢#τ∈✶ Γ⊢#τ∈✶')
  rewrite eq rewrite proj₂ (sing-inv-∙∙ τ K refl) rewrite un-∙∙ eq =
    k-sing-# Γ⊢#τ∈✶
sing-incl-# {Γ = Γ} {τ = τ} {K = K} eq (wf-darr-# Γ⊢#Jkd Γx∶J⊢S[τ∈K]kd)
    rewrite eq = foo
  where
    -- TODO: need to show that singletons preserve opening
    postulate
      foo : Γ ⊢#ty τ ∈ S[ τ ∈ K ]

-- TODO: This construction requires subkind transitivity, but we could possibly
-- avoid it by baking the proof of [Γ ⊢#kd τ ∈ K] in directly.
record KSelPremise (Γ : Context) (x : Var) (M : TypeLabel) (K : Kind) : Set where
  constructor KS
  field
    τ : Type
    J : Kind
    Γ⊢#τ∈J : Γ ⊢#ty τ ∈ J
    Γ⊢#J≤K : Γ ⊢#kd J ≤ K
    U : Type
    Γ⊢!x∈S[τ∶J] : Γ ⊢!var x ∈ U ⟫ [ typ M ∶ S[ τ ∈ J ] ]

k-sel-premise : ∀ {Γ x M K} →
  Γ inert-ctx →
  Γ ⊢#tm ` x ∈ [ typ M ∶ K ] →
  KSelPremise Γ x M K
k-sel-premise {Γ} {x} {M} {k} Γinert Γ⊢#x∈[M∶k] =
    k-sel-premise-## (⊢#→⊢##-var Γinert Γ⊢#x∈[M∶k])
  where
    k-sel-premise-## : ∀ {K} → Γ ⊢##var x ∈ [ typ M ∶ K ] → KSelPremise Γ x M K

    k-sel-premise-## (ty-precise-## {τ = U} Γ⊢!x∈U⟫[M∶K])
      with precise-recd-kind-is-singleton Γinert Γ⊢!x∈U⟫[M∶K]
    ... | Sing τ J eq rewrite eq = KS
        τ
        S[τ∈J]
        (sing-incl-# refl Γ⊢#S[τ∈J]kd)
        (sk-refl-# S[τ∈J])
        U
        Γ⊢!x∈[M∶S[τ∈S[τ∈J]]]
      where
        S[τ∈J] = S[ τ ∈ J ]

        Γ⊢!x∈[M∶S[τ∈S[τ∈J]]] : Γ ⊢!var x ∈ U ⟫ [ typ M ∶ S[ τ ∈ S[ τ ∈ J ] ] ]
        Γ⊢!x∈[M∶S[τ∈S[τ∈J]]] rewrite sing-idempotent τ J = Γ⊢!x∈U⟫[M∶K]

        Γ⊢#x∈[M∶S[τ∈J]] = ⊢##→⊢#-var (ty-precise-## Γ⊢!x∈U⟫[M∶K])
        Γ⊢#[M∶S[τ∈J]]∈K' = types-wf-# Γ⊢#x∈[M∶S[τ∈J]]

        unwrap : ∀{K} → Γ ⊢#ty [ typ M ∶ S[ τ ∈ J ] ] ∈ K → Γ ⊢# S[ τ ∈ J ] kd
        unwrap (k-sing-# Γ⊢#[M∶S[τ∈J]]∈S∙∙U) = unwrap Γ⊢#[M∶S[τ∈J]]∈S∙∙U
        unwrap (k-sub-# Γ⊢#[M∶S[τ∈J]]∈K' Γ⊢#K'≤K) = unwrap Γ⊢#[M∶S[τ∈J]]∈K'
        unwrap (k-typ-# Γ⊢#S[τ∈J]kd) = Γ⊢#S[τ∈J]kd

        Γ⊢#S[τ∈J]kd = unwrap (proj₂ Γ⊢#[M∶S[τ∈J]]∈K')

    k-sel-premise-## (ty-type-## Γ⊢##x∈[M∶J] Γ⊢#J≤K) =
      let KS τ J' Γ⊢#τ∈J' Γ⊢#J'≤J U Γ⊢!x∈U⟫[M∶S[τ∶J']] =
            k-sel-premise-## Γ⊢##x∈[M∶J]
          Γ⊢#τ∈J = k-sub-# Γ⊢#τ∈J' Γ⊢#J'≤J
          Γ⊢#J'≤K = sk-trans-# Γ⊢#J'≤J Γ⊢#J≤K
       in
      KS τ J' Γ⊢#τ∈J' Γ⊢#J'≤K U Γ⊢!x∈U⟫[M∶S[τ∶J']]

-- The main proof, converting general typing [Γ ⊢ty e ∈ τ] to tight typing
-- [Γ ⊢#ty e ∈ τ].
--
-- Instead of structural induction on the typing derivation itself, we perform
-- natural induction on the height of the derivation tree. This is necessary
-- because we have to narrow one of the premises in the [st-β] cases before
-- citing the inductive hypothesis, which will freak out the termination
-- checker if done naively.
--
-- Unfortunately, these rules are inherently extremely mutually recursive,
-- which means we need to use mutually well-founded recursion. To make it more
-- manageable, we unify each general typing judgment into the single [Judgment]
-- type. For more information on using GADTs for well-founded mutual recursion,
-- check out this blog post:
--
-- (TODO: write blog post)
--
-- The main body of this proof is the function ⊢→⊢#-step.

data Judgment : Context → Set → Set where
  IsCtx : ∀{Γ} → Γ ctx → Judgment Γ (Γ ctx-#)
  Typing : ∀{Γ e τ} → Γ ⊢tm e ∈ τ → Judgment Γ (Γ ⊢#tm e ∈ τ)
  Subtyping : ∀{Γ S U K} → Γ ⊢ty S ≤ U ∈ K → Judgment Γ (Γ ⊢#ty S ≤ U ∈ K)
  IsKd : ∀{Γ K} → Γ ⊢ K kd → Judgment Γ (Γ ⊢# K kd)
  Kinding : ∀{Γ τ K} → Γ ⊢ty τ ∈ K → Judgment Γ (Γ ⊢#ty τ ∈ K)
  Subkinding : ∀{Γ J K} → Γ ⊢kd J ≤ K → Judgment Γ (Γ ⊢#kd J ≤ K)

Judgment-height : ∀ {Γ Out} → Judgment Γ Out → ℕ
Judgment-height (IsCtx Γctx) = []ctx-h Γctx
Judgment-height (Typing Γ⊢e∈τ) = ⊢tm[]∈[]-h Γ⊢e∈τ
Judgment-height (Subtyping Γ⊢S≤U∈K) = ⊢ty[]≤[]∈[]-h Γ⊢S≤U∈K
Judgment-height (IsKd Γ⊢K-kd) = ⊢[]kd-h Γ⊢K-kd
Judgment-height (Kinding Γ⊢τ∈K) = ⊢ty[]∈[]-h Γ⊢τ∈K
Judgment-height (Subkinding Γ⊢J≤K) = ⊢kd[]≤[]-h Γ⊢J≤K

PackedJudgment : Set (lsuc lzero)
PackedJudgment = Σ[ p ∈ Context × Set ](Judgment (proj₁ p) (proj₂ p))

unpack : PackedJudgment → Set
unpack ((Γ , Out) , j) = Γ inert-ctx → Out

PackedJudgment-height : PackedJudgment → ℕ
PackedJudgment-height (_ , j) = Judgment-height j

_<_ : PackedJudgment → PackedJudgment → Set
j < j' = PackedJudgment-height j <ℕ PackedJudgment-height j'

<-wf : ∀ j → Acc _<_ j
<-wf = accMeasure PackedJudgment-height

⊢→⊢#-step : ∀ (packed@((Γ , Out) , j) : PackedJudgment) →
  Γ inert-ctx →
  Acc _<_ packed →
  Out

-- Context validity
⊢→⊢#-step (_ , (IsCtx c-empty)) Γinert (acc rec) = c-empty-#
⊢→⊢#-step (_ , (IsCtx (c-cons-ty Γctx Γ⊢τ∈K))) Γx-inert (acc rec) =
  let Γinert = unwrap-inert-ctx Γx-inert
   in
  c-cons-ty-#
    (⊢→⊢#-step (_ , IsCtx Γctx) Γinert (rec _ (s≤s (m≤m⊔n _ _))))
    (⊢→⊢#-step (_ , Kinding Γ⊢τ∈K) Γinert (rec _ (s≤s (m≤n⊔m _ _))))
⊢→⊢#-step (_ , (IsCtx (c-cons-kd Γctx Γ⊢K-kd))) Γx-inert (acc rec) =
  let Γinert = unwrap-inert-ctx Γx-inert
   in
  c-cons-kd-#
    (⊢→⊢#-step (_ , IsCtx Γctx) Γinert (rec _ (s≤s (m≤m⊔n _ _))))
    (⊢→⊢#-step (_ , IsKd Γ⊢K-kd) Γinert (rec _ (s≤s (m≤n⊔m _ _))))

-- Type assignment
⊢→⊢#-step (_ , Typing (ty-var Γ[x]⊢>τ)) Γinert (acc rec) = ty-var-# Γ[x]⊢>τ
⊢→⊢#-step (_ , Typing (ty-ℿ-intro Γ⊢e∈τ)) Γinert (acc rec) = ty-ℿ-intro-# Γ⊢e∈τ
⊢→⊢#-step (_ , Typing (ty-ℿ-elim Γ⊢f∈τ₁⇒τ₂ Γ⊢x∈τ₁)) Γinert (acc rec) =
  ty-ℿ-elim-#
    (⊢→⊢#-step (_ , Typing Γ⊢f∈τ₁⇒τ₂) Γinert (rec _ (s≤s (m≤m⊔n _ _))))
    (⊢→⊢#-step (_ , Typing Γ⊢x∈τ₁) Γinert (rec _ (s≤s (m≤n⊔m _ _))))
⊢→⊢#-step (_ , Typing (ty-new-intro Γ⊢defs∈τ)) Γinert (acc rec) =
  ty-new-intro-# Γ⊢defs∈τ
⊢→⊢#-step (_ , Typing (ty-new-elim Γ⊢x∈[val])) Γinert (acc rec) =
  ty-new-elim-#
    (⊢→⊢#-step (_ , Typing Γ⊢x∈[val]) Γinert (rec _ (s≤s (≤-reflexive refl))))
⊢→⊢#-step (_ , Typing (ty-let Γ⊢e₁∈τ Γ⊢e₂∈ρ)) Γinert (acc rec) =
  ty-let-#
    (⊢→⊢#-step (_ , Typing Γ⊢e₁∈τ) Γinert (rec _ (s≤s (m≤m⊔n _ _)))) Γ⊢e₂∈ρ
⊢→⊢#-step (_ , Typing (ty-rec-intro Γ⊢x∈τ)) Γinert (acc rec) =
  ty-rec-intro-#
    (⊢→⊢#-step (_ , Typing Γ⊢x∈τ) Γinert (rec _ (s≤s (≤-reflexive refl))))
⊢→⊢#-step (_ , Typing (ty-rec-elim Γ⊢x∈μτ)) Γinert (acc rec) =
  ty-rec-elim-#
    (⊢→⊢#-step (_ , Typing Γ⊢x∈μτ) Γinert (rec _ (s≤s (≤-reflexive refl))))
⊢→⊢#-step (_ , Typing (ty-and-intro Γ⊢x∈τ₁ Γ⊢x∈τ₂)) Γinert (acc rec) =
    ty-and-intro-#
      (⊢→⊢#-step (_ , Typing Γ⊢x∈τ₁) Γinert (rec _ (s≤s (m≤m⊔n _ _))))
      (⊢→⊢#-step (_ , Typing Γ⊢x∈τ₂) Γinert (rec _ (s≤s (m≤n⊔m _ _))))
⊢→⊢#-step (_ , Typing (ty-sub Γ⊢e∈τ₁ Γ⊢τ₁≤τ₂)) Γinert (acc rec) =
    ty-sub-#
      (⊢→⊢#-step (_ , Typing Γ⊢e∈τ₁) Γinert (rec _ (s≤s (m≤m⊔n _ _))))
      (⊢→⊢#-step (_ , Subtyping Γ⊢τ₁≤τ₂) Γinert (rec _ (s≤s (m≤n⊔m _ _))))

-- Subtyping
⊢→⊢#-step (_ , Subtyping (st-refl Γ⊢A∈K)) Γinert (acc rec) =
  st-refl-# (⊢→⊢#-step (_ , Kinding Γ⊢A∈K) Γinert (rec _ (s≤s (≤-reflexive refl))))
⊢→⊢#-step (_ , Subtyping (st-trans Γ⊢A≤B Γ⊢B≤C)) Γinert (acc rec) =
  st-trans-#
    (⊢→⊢#-step (_ , Subtyping Γ⊢A≤B) Γinert (rec _ (s≤s (m≤m⊔n _ _))))
    (⊢→⊢#-step (_ , Subtyping Γ⊢B≤C) Γinert (rec _ (s≤s (m≤n⊔m _ _))))
⊢→⊢#-step (_ , Subtyping (st-top Γ⊢A∈S∙∙U)) Γinert (acc rec) =
  st-top-# (⊢→⊢#-step (_ , Kinding Γ⊢A∈S∙∙U) Γinert (rec _ (s≤s (≤-reflexive refl))))
⊢→⊢#-step (_ , Subtyping (st-bot Γ⊢A∈S∙∙U)) Γinert (acc rec) =
  st-bot-# (⊢→⊢#-step (_ , Kinding Γ⊢A∈S∙∙U) Γinert (rec _ (s≤s (≤-reflexive refl))))
⊢→⊢#-step (_ , Subtyping (st-and-l₁ Γ⊢τ₁∧τ₂∈K)) Γinert (acc rec) =
  st-and-l₁-# (⊢→⊢#-step (_ , Kinding Γ⊢τ₁∧τ₂∈K) Γinert (rec _ (s≤s (≤-reflexive refl))))
⊢→⊢#-step (_ , Subtyping (st-and-l₂ Γ⊢τ₁∧τ₂∈K)) Γinert (acc rec) =
  st-and-l₂-# (⊢→⊢#-step (_ , Kinding Γ⊢τ₁∧τ₂∈K) Γinert (rec _ (s≤s (≤-reflexive refl))))
⊢→⊢#-step (_ , Subtyping (st-and₂ Γ⊢ρ≤τ₁∈K Γ⊢ρ≤τ₂∈K)) Γinert (acc rec) =
  st-and₂-#
    (⊢→⊢#-step (_ , Subtyping Γ⊢ρ≤τ₁∈K) Γinert (rec _ (s≤s (m≤m⊔n _ _))))
    (⊢→⊢#-step (_ , Subtyping Γ⊢ρ≤τ₂∈K) Γinert (rec _ (s≤s (m≤n⊔m _ _))))
⊢→⊢#-step (_ , Subtyping (st-field Γ⊢τ₁≤τ₂∈K)) Γinert (acc rec) =
  st-field-# (⊢→⊢#-step (_ , Subtyping Γ⊢τ₁≤τ₂∈K) Γinert (rec _ (s≤s (≤-reflexive refl))))
⊢→⊢#-step (_ , Subtyping (st-typ Γ⊢J≤K)) Γinert (acc rec) =
  st-typ-# (⊢→⊢#-step (_ , Subkinding Γ⊢J≤K) Γinert (rec _ (s≤s (≤-reflexive refl))))
⊢→⊢#-step (_ , Subtyping t@(st-app Γ⊢A₁≤A₂ e@(st-antisym Γ⊢B₁≤B₂ Γ⊢B₂≤B₁))) Γinert (acc rec) =
  st-app-#
    (⊢→⊢#-step (_ , Subtyping Γ⊢A₁≤A₂) Γinert (rec _ (s≤s (m≤m⊔n _ _))))
    (st-antisym-#
      (⊢→⊢#-step (_ , Subtyping Γ⊢B₁≤B₂) Γinert (rec _ p1))
      (⊢→⊢#-step (_ , Subtyping Γ⊢B₂≤B₁) Γinert (rec _ p2)))
  where
    open Data.Nat.Properties.≤-Reasoning

    p1 : ⊢ty[]≤[]∈[]-h Γ⊢B₁≤B₂ <ℕ ⊢ty[]≤[]∈[]-h t
    p1 = begin-strict
        ⊢ty[]≤[]∈[]-h Γ⊢B₁≤B₂
      <⟨ s≤s (m≤m⊔n _ _) ⟩
        suc (⊢ty[]≤[]∈[]-h Γ⊢B₁≤B₂ ⊔ ⊢ty[]≤[]∈[]-h Γ⊢B₂≤B₁)
      <⟨ s≤s (m≤n⊔m _ _) ⟩
        suc (⊢ty[]≤[]∈[]-h Γ⊢A₁≤A₂ ⊔ ⊢ty[]==[]-h e)
      ≡⟨⟩
        ⊢ty[]≤[]∈[]-h t
      ∎

    p2 : ⊢ty[]≤[]∈[]-h Γ⊢B₂≤B₁ <ℕ ⊢ty[]≤[]∈[]-h t
    p2 = begin-strict
        ⊢ty[]≤[]∈[]-h Γ⊢B₂≤B₁
      <⟨ s≤s (m≤n⊔m _ _) ⟩
        suc (⊢ty[]≤[]∈[]-h Γ⊢B₁≤B₂ ⊔ ⊢ty[]≤[]∈[]-h Γ⊢B₂≤B₁)
      <⟨ s≤s (m≤n⊔m _ _) ⟩
        suc (⊢ty[]≤[]∈[]-h Γ⊢A₁≤A₂ ⊔ ⊢ty[]==[]-h e)
      ≡⟨⟩
        ⊢ty[]≤[]∈[]-h t
      ∎
⊢→⊢#-step (_ , Subtyping (st-bnd₁ Γ⊢A∈S∙∙U)) Γinert (acc rec) =
  st-bnd₁-# (⊢→⊢#-step (_ , Kinding Γ⊢A∈S∙∙U) Γinert (rec _ (s≤s (≤-reflexive refl))))
⊢→⊢#-step (_ , Subtyping (st-bnd₂ Γ⊢A∈S∙∙U)) Γinert (acc rec) =
  st-bnd₂-# (⊢→⊢#-step (_ , Kinding Γ⊢A∈S∙∙U) Γinert (rec _ (s≤s (≤-reflexive refl))))

-- TODO/paper: lemma numbering
-- This step corresponds to Lemma ## in the paper. It is inlined, rather than
-- separated into its own lemma, to ease the already-nasty well-founded
-- recursion necessary here.
⊢→⊢#-step ((Γ , _) , Subtyping (st-β₁ {J} {K} {x} {A} {B} Γx∶J⊢A∈K Γ⊢B∈J)) Γinert (acc rec) =
    st-β₁-#
      (⊢→⊢#-step (_ , Kinding Γ⊢B∈J) Γinert (rec _ (s≤s (m≤n⊔m _ _))))
      Γx∶S[B∈J]⊢#A∈K
  where
    narrowed : Σ[ p ∈ Γ & x ~ Kd S[ B ∈ J ] ⊢ty openType x A ∈ K ]
      (⊢ty[]∈[]-h Γx∶J⊢A∈K ≡ ⊢ty[]∈[]-h p)
    narrowed = narrowing-sk-kd Γx∶J⊢A∈K (sing-sub Γ⊢B∈J)

    Γx∶S[B∈J]⊢A∈K : Γ & x ~ Kd S[ B ∈ J ] ⊢ty openType x A ∈ K
    Γx∶S[B∈J]⊢A∈K = proj₁ narrowed

    -- the height of the narrowed subtree is the same as the original, so...
    height-eq : ⊢ty[]∈[]-h Γx∶J⊢A∈K ≡ ⊢ty[]∈[]-h Γx∶S[B∈J]⊢A∈K
    height-eq = proj₂ narrowed

    -- ...we can cite the inductive hypothesis on it.
    Γx∶S[B∈J]⊢#A∈K : Γ & x ~ Kd S[ B ∈ J ] ⊢#ty openType x A ∈ K
    Γx∶S[B∈J]⊢#A∈K rewrite height-eq = ⊢→⊢#-step
      (_ , Kinding Γx∶S[B∈J]⊢A∈K)
      (cons-inert-kd Γinert (sing-inert B J))
      (rec _ (s≤s (m≤m⊔n _ _)))

⊢→⊢#-step ((Γ , _) , Subtyping (st-β₂ {J} {K} {x} {A} {B} Γx∶J⊢A∈K Γ⊢B∈J)) Γinert (acc rec) =
    st-β₂-#
      (⊢→⊢#-step (_ , Kinding Γ⊢B∈J) Γinert (rec _ (s≤s (m≤n⊔m _ _))))
      Γx∶S[B∈J]⊢#A∈K
  where
    narrowed : Σ[ p ∈ Γ & x ~ Kd S[ B ∈ J ] ⊢ty openType x A ∈ K ]
      (⊢ty[]∈[]-h Γx∶J⊢A∈K ≡ ⊢ty[]∈[]-h p)
    narrowed = narrowing-sk-kd Γx∶J⊢A∈K (sing-sub Γ⊢B∈J)

    Γx∶S[B∈J]⊢A∈K : Γ & x ~ Kd S[ B ∈ J ] ⊢ty openType x A ∈ K
    Γx∶S[B∈J]⊢A∈K = proj₁ narrowed

    height-eq : ⊢ty[]∈[]-h Γx∶J⊢A∈K ≡ ⊢ty[]∈[]-h Γx∶S[B∈J]⊢A∈K
    height-eq = proj₂ narrowed

    Γx∶S[B∈J]⊢#A∈K : Γ & x ~ Kd S[ B ∈ J ] ⊢#ty openType x A ∈ K
    Γx∶S[B∈J]⊢#A∈K rewrite height-eq = ⊢→⊢#-step
      (_ , Kinding Γx∶S[B∈J]⊢A∈K)
      (cons-inert-kd Γinert (sing-inert B J))
      (rec _ (s≤s (m≤m⊔n _ _)))

-- Kind assignment
⊢→⊢#-step (_ , Kinding (k-var Γctx Γ[x]⊢>τ)) Γinert (acc rec) =
  k-var-#
    (⊢→⊢#-step (_ , IsCtx Γctx) Γinert (rec _ (s≤s (≤-reflexive refl))))
    Γ[x]⊢>τ
⊢→⊢#-step (_ , Kinding k-top) Γinert (acc rec) = k-top-#
⊢→⊢#-step (_ , Kinding k-bot) Γinert (acc rec) = k-bot-#
⊢→⊢#-step (_ , Kinding (k-sing Γ⊢A∈S∙∙U)) Γinert (acc rec) =
  k-sing-#
    (⊢→⊢#-step (_ , Kinding Γ⊢A∈S∙∙U) Γinert (rec _ (s≤s (≤-reflexive refl))))
⊢→⊢#-step (_ , Kinding (k-arr Γ⊢A∈✶ Γ⊢B∈✶)) Γinert (acc rec) =
  k-arr-#
    (⊢→⊢#-step (_ , Kinding Γ⊢A∈✶) Γinert (rec _ (s≤s (m≤m⊔n _ _))))
    Γ⊢B∈✶
⊢→⊢#-step (_ , Kinding (k-abs Γ⊢J-kd Γ⊢A∈K)) Γinert (acc rec) =
  k-abs-#
    (⊢→⊢#-step (_ , IsKd Γ⊢J-kd) Γinert (rec _ (s≤s (m≤m⊔n _ _))))
    Γ⊢A∈K
⊢→⊢#-step (_ , Kinding (k-app Γ⊢f∈ℿJK Γ⊢τ∈J)) Γinert (acc rec) =
  k-app-#
    (⊢→⊢#-step (_ , Kinding Γ⊢f∈ℿJK) Γinert (rec _ (s≤s (m≤m⊔n _ _))))
    (⊢→⊢#-step (_ , Kinding Γ⊢τ∈J) Γinert (rec _ (s≤s (m≤n⊔m _ _))))
⊢→⊢#-step (_ , Kinding (k-intersect Γ⊢τ₁∈S₁∙∙U₁ Γ⊢τ₂∈S₂∙∙U₂)) Γinert (acc rec) =
  k-intersect-#
    (⊢→⊢#-step (_ , Kinding Γ⊢τ₁∈S₁∙∙U₁) Γinert (rec _ (s≤s (m≤m⊔n _ _))))
    (⊢→⊢#-step (_ , Kinding Γ⊢τ₂∈S₂∙∙U₂) Γinert (rec _ (s≤s (m≤n⊔m _ _))))
⊢→⊢#-step (_ , Kinding (k-sub Γ⊢τ∈J Γ⊢J≤K)) Γinert (acc rec) =
  k-sub-#
    (⊢→⊢#-step (_ , Kinding Γ⊢τ∈J) Γinert (rec _ (s≤s (m≤m⊔n _ _))))
    (⊢→⊢#-step (_ , Subkinding Γ⊢J≤K) Γinert (rec _ (s≤s (m≤n⊔m _ _))))
⊢→⊢#-step (_ , Kinding (k-field Γ⊢τ∈A∙∙B)) Γinert (acc rec) =
  k-field-#
    (⊢→⊢#-step (_ , Kinding Γ⊢τ∈A∙∙B) Γinert (rec _ (s≤s (≤-reflexive refl))))
⊢→⊢#-step (_ , Kinding (k-typ Γ⊢K-kd)) Γinert (acc rec) =
  k-typ-#
    (⊢→⊢#-step (_ , IsKd Γ⊢K-kd) Γinert (rec _ (s≤s (≤-reflexive refl))))
⊢→⊢#-step (_ , Kinding (k-sel Γ⊢x∈[M∶K])) Γinert (acc rec) =
  let KS τ J Γ⊢#τ∈J Γ⊢#J≤K U Γ⊢!x∈[M∶S[J]] =
        k-sel-premise
          Γinert
          (⊢→⊢#-step
            (_ , Typing Γ⊢x∈[M∶K])
            Γinert
            (rec _ (s≤s (≤-reflexive refl))))
      Γ⊢#x∙M∈S[J] = k-sel-# Γ⊢!x∈[M∶S[J]]
      Γ⊢#S[J]≤J = sing-sub-# Γ⊢#τ∈J
      Γ⊢#x∙M∈J = k-sub-# Γ⊢#x∙M∈S[J] Γ⊢#S[J]≤J
      Γ⊢#x∙M∈K = k-sub-# Γ⊢#x∙M∈J Γ⊢#J≤K
   in
  Γ⊢#x∙M∈K

-- Kind validity
⊢→⊢#-step (_ , IsKd (wf-intv Γ⊢S∈✶ Γ⊢U∈✶)) Γinert (acc rec) =
  wf-intv-#
    (⊢→⊢#-step (_ , Kinding Γ⊢S∈✶) Γinert (rec _ (s≤s (m≤m⊔n _ _))))
    (⊢→⊢#-step (_ , Kinding Γ⊢U∈✶) Γinert (rec _ (s≤s (m≤n⊔m _ _))))
⊢→⊢#-step (_ , IsKd (wf-darr Γ⊢J-kd Γ⊢K-kd)) Γinert (acc rec) =
  wf-darr-#
    (⊢→⊢#-step (_ , IsKd Γ⊢J-kd) Γinert (rec _ (s≤s (m≤m⊔n _ _))))
    Γ⊢K-kd

-- Subkinding
⊢→⊢#-step (_ , Subkinding (sk-intv Γ⊢S₂≤S₁ Γ⊢U₁≤U₂)) Γinert (acc rec) =
  sk-intv-#
    (⊢→⊢#-step (_ , Subtyping Γ⊢S₂≤S₁) Γinert (rec _ (s≤s (m≤m⊔n _ _))))
    (⊢→⊢#-step (_ , Subtyping Γ⊢U₁≤U₂) Γinert (rec _ (s≤s (m≤n⊔m _ _))))
⊢→⊢#-step (_ , Subkinding t@(sk-darr Γ⊢ℿJ₁K₁-kd Γ⊢J₂≤J₁ Γ⊢K₁≤K₂)) Γinert (acc rec) =
  sk-darr-#
    (⊢→⊢#-step (_ , IsKd Γ⊢ℿJ₁K₁-kd) Γinert (rec _ (s≤s (≤-trans (m≤m⊔n _ _) (m≤m⊔n _ _)))))
    (⊢→⊢#-step (_ , Subkinding Γ⊢J₂≤J₁) Γinert (rec _ p))
    Γ⊢K₁≤K₂
  where
    open Data.Nat.Properties.≤-Reasoning

    p : ⊢kd[]≤[]-h Γ⊢J₂≤J₁ <ℕ ⊢kd[]≤[]-h t
    p = begin-strict
        ⊢kd[]≤[]-h Γ⊢J₂≤J₁
      ≤⟨ m≤n⊔m _ _ ⟩
        ⊢[]kd-h Γ⊢ℿJ₁K₁-kd ⊔ ⊢kd[]≤[]-h Γ⊢J₂≤J₁
      ≤⟨ m≤m⊔n _ _ ⟩
        ⊢[]kd-h Γ⊢ℿJ₁K₁-kd ⊔ ⊢kd[]≤[]-h Γ⊢J₂≤J₁ ⊔ ⊢kd[]≤[]-h Γ⊢K₁≤K₂
      <⟨ s≤s (≤-reflexive refl) ⟩
        suc (⊢[]kd-h Γ⊢ℿJ₁K₁-kd ⊔ ⊢kd[]≤[]-h Γ⊢J₂≤J₁ ⊔ ⊢kd[]≤[]-h Γ⊢K₁≤K₂)
      ≡⟨⟩
        ⊢kd[]≤[]-h t
      ∎

-- Convenience aliases

⊢→⊢# : ∀ {Γ Out} → Γ inert-ctx → Judgment Γ Out → Out
⊢→⊢# {Γ} {Out} Γinert j = ⊢→⊢#-step ((Γ , Out) , j) Γinert (<-wf ((Γ , Out) , j))

⊢→⊢#-tm : ∀ {Γ e τ} → Γ inert-ctx → Γ ⊢tm e ∈ τ → Γ ⊢#tm e ∈ τ
⊢→⊢#-tm Γinert p = ⊢→⊢# Γinert (Typing p)

⊢→⊢#-st : ∀ {Γ S U k} → Γ inert-ctx → Γ ⊢ty S ≤ U ∈ k → Γ ⊢#ty S ≤ U ∈ k
⊢→⊢#-st Γinert p = ⊢→⊢# Γinert (Subtyping p)

⊢→⊢#-ty : ∀ {Γ τ k} → Γ inert-ctx → Γ ⊢ty τ ∈ k → Γ ⊢#ty τ ∈ k
⊢→⊢#-ty Γinert p = ⊢→⊢# Γinert (Kinding p)

⊢→⊢#-sk : ∀ {Γ J K} → Γ inert-ctx → Γ ⊢kd J ≤ K → Γ ⊢#kd J ≤ K
⊢→⊢#-sk Γinert p = ⊢→⊢# Γinert (Subkinding p)

⊢→⊢#-kd : ∀ {Γ k} → Γ inert-ctx → Γ ⊢ k kd → Γ ⊢# k kd
⊢→⊢#-kd Γinert p = ⊢→⊢# Γinert (IsKd p)

