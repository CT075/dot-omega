open import Level renaming (zero to lzero; suc to lsuc) hiding (Lift; _⊔_)
open import Relation.Binary using (DecSetoid)

module DOTOmega.Typing.Properties
    (TypeL : DecSetoid lzero lzero)
    (TermL : DecSetoid lzero lzero)
  where

open import Data.Bool using (true; false; if_then_else_)
open import Data.Nat using (ℕ; _⊔_; zero; suc)
open import Data.List using ([]; map)
open import Data.Empty using (⊥-elim) renaming (⊥ to Void)
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Nullary.Decidable using (Dec; isYes)
open import Relation.Binary.PropositionalEquality

open import Data.Var
open import Data.Var.Properties using (_≟_)
open import Data.Context
open import Data.Context.Properties

open import DOTOmega.Syntax TypeL TermL
open import DOTOmega.Typing TypeL TermL

typed-var-is-free : ∀ {Γ var τ} →
  Γ ⊢tm ` var ∈ τ →
  Σ[ x ∈ Name ](var ≡ Free x)
typed-var-is-free (ty-var {name} Γ[name]⊢>τ) = (name , refl)
typed-var-is-free (ty-rec-intro Γ⊢var∈τ) = typed-var-is-free Γ⊢var∈τ
typed-var-is-free (ty-rec-elim Γ⊢var∈τ) = typed-var-is-free Γ⊢var∈τ
typed-var-is-free (ty-and-intro Γ⊢var∈S Γ⊢var∈U) = typed-var-is-free Γ⊢var∈S
typed-var-is-free (ty-sub Γ⊢var∈S S≤U) = typed-var-is-free Γ⊢var∈S

postulate
  weakening-tm-sk : ∀ {Γ x τ J K} →
    Γ ⊢kd J ≤ K →
    Γ & x ~ Ty τ ⊢kd J ≤ K

  typing-validity : ∀ {Γ e τ} → Γ ⊢tm e ∈ τ → Γ ⊢ty τ ∈ ✶

-- Induction measures

-- TODO: this is all boilerplate, maybe replace with sized types

mutual
  []ctx-h : ∀{Γ} → Γ ctx → ℕ
  []ctx-h c-empty = 1
  []ctx-h (c-cons-kd Γctx Γ⊢Kkd) = suc ([]ctx-h Γctx ⊔ ⊢[]kd-h Γ⊢Kkd)
  []ctx-h (c-cons-ty Γctx Γ⊢τ∈k) = suc ([]ctx-h Γctx ⊔ ⊢ty[]∈[]-h Γ⊢τ∈k)

  ⊢[]kd-h : ∀{Γ k} → Γ ⊢ k kd → ℕ
  ⊢[]kd-h (wf-intv Γ⊢S∈✶ Γ⊢U∈✶) = suc (⊢ty[]∈[]-h Γ⊢S∈✶ ⊔ ⊢ty[]∈[]-h Γ⊢U∈✶)
  ⊢[]kd-h (wf-darr Γ⊢Jkd Γx⊢Kkd) = suc (⊢[]kd-h Γ⊢Jkd ⊔ ⊢[]kd-h Γx⊢Kkd)

  ⊢kd[]≤[]-h : ∀{Γ J K} → Γ ⊢kd J ≤ K → ℕ
  ⊢kd[]≤[]-h (sk-intv Γ⊢S₂≤S₁ Γ⊢U₁≤U₂) =
    suc (⊢ty[]≤[]∈[]-h Γ⊢S₂≤S₁ ⊔ ⊢ty[]≤[]∈[]-h Γ⊢U₁≤U₂)
  ⊢kd[]≤[]-h (sk-darr Γ⊢ℿJ₁K₁kd Γ⊢J₂≤J₁ Γx⊢K₁≤K₂) =
    suc (⊢[]kd-h Γ⊢ℿJ₁K₁kd ⊔ ⊢kd[]≤[]-h Γ⊢J₂≤J₁ ⊔ ⊢kd[]≤[]-h Γx⊢K₁≤K₂)

  ⊢ty[]∈[]-h : ∀{Γ τ K} → Γ ⊢ty τ ∈ K → ℕ
  ⊢ty[]∈[]-h (k-var Γctx Γ[x]⊢τ) = suc ([]ctx-h Γctx)
  ⊢ty[]∈[]-h k-top = 1
  ⊢ty[]∈[]-h k-bot = 1
  ⊢ty[]∈[]-h (k-sing Γ⊢A∈S∙∙U) = suc (⊢ty[]∈[]-h Γ⊢A∈S∙∙U)
  ⊢ty[]∈[]-h (k-arr Γ⊢A∈✶ Γ⊢B∈✶) = suc (⊢ty[]∈[]-h Γ⊢A∈✶ ⊔ ⊢ty[]∈[]-h Γ⊢B∈✶)
  ⊢ty[]∈[]-h (k-abs Γ⊢Jkd Γx⊢A∈K) = suc (⊢[]kd-h Γ⊢Jkd ⊔ ⊢ty[]∈[]-h Γx⊢A∈K)
  ⊢ty[]∈[]-h (k-app Γ⊢f∈ℿJK Γ⊢τ∈J) = suc (⊢ty[]∈[]-h Γ⊢f∈ℿJK ⊔ ⊢ty[]∈[]-h Γ⊢τ∈J)
  ⊢ty[]∈[]-h (k-intersect Γ⊢A∈K₁ Γ⊢A∈K₂) =
    suc (⊢ty[]∈[]-h Γ⊢A∈K₁ ⊔ ⊢ty[]∈[]-h Γ⊢A∈K₂)
  ⊢ty[]∈[]-h (k-sub Γ⊢A∈J Γ⊢J≤K) = suc (⊢ty[]∈[]-h Γ⊢A∈J ⊔ ⊢kd[]≤[]-h Γ⊢J≤K)
  ⊢ty[]∈[]-h (k-field Γ⊢τ∈S∙∙U) = suc (⊢ty[]∈[]-h Γ⊢τ∈S∙∙U)
  ⊢ty[]∈[]-h (k-typ Γ⊢Kkd) = suc (⊢[]kd-h Γ⊢Kkd)
  ⊢ty[]∈[]-h (k-sel Γ⊢x∈[M∶k]) = suc (⊢tm[]∈[]-h Γ⊢x∈[M∶k])
  ⊢ty[]∈[]-h (k-rec Γx⊢xτ∈✶) = suc (⊢ty[]∈[]-h Γx⊢xτ∈✶)

  ⊢ty[]≤[]∈[]-h : ∀{Γ A B K} → Γ ⊢ty A ≤ B ∈ K → ℕ
  ⊢ty[]≤[]∈[]-h (st-refl Γ⊢A∈K) = suc (⊢ty[]∈[]-h Γ⊢A∈K)
  ⊢ty[]≤[]∈[]-h (st-trans Γ⊢A≤B Γ⊢B≤C) =
    suc (⊢ty[]≤[]∈[]-h Γ⊢A≤B ⊔ ⊢ty[]≤[]∈[]-h Γ⊢B≤C)
  ⊢ty[]≤[]∈[]-h (st-top Γ⊢A∈✶) = suc (⊢ty[]∈[]-h Γ⊢A∈✶)
  ⊢ty[]≤[]∈[]-h (st-bot Γ⊢A∈✶) = suc (⊢ty[]∈[]-h Γ⊢A∈✶)
  ⊢ty[]≤[]∈[]-h (st-and-l₁ Γ⊢τ₁∧τ₂∈K) = suc (⊢ty[]∈[]-h Γ⊢τ₁∧τ₂∈K)
  ⊢ty[]≤[]∈[]-h (st-and-l₂ Γ⊢τ₁∧τ₂∈K) = suc (⊢ty[]∈[]-h Γ⊢τ₁∧τ₂∈K)
  ⊢ty[]≤[]∈[]-h (st-and₂ Γ⊢ρ≤τ₁ Γ⊢ρ≤τ₂) =
    suc (⊢ty[]≤[]∈[]-h Γ⊢ρ≤τ₁ ⊔ ⊢ty[]≤[]∈[]-h Γ⊢ρ≤τ₂)
  ⊢ty[]≤[]∈[]-h (st-abs Γ⊢S₂≤S₁ Γx⊢xT₁≤xT₂) =
    suc (⊢ty[]≤[]∈[]-h Γ⊢S₂≤S₁ ⊔ ⊢ty[]≤[]∈[]-h Γx⊢xT₁≤xT₂)
  ⊢ty[]≤[]∈[]-h (st-field Γ⊢τ₁≤τ₂) = suc (⊢ty[]≤[]∈[]-h Γ⊢τ₁≤τ₂)
  ⊢ty[]≤[]∈[]-h (st-typ Γ⊢J≤K) = suc (⊢kd[]≤[]-h Γ⊢J≤K)
  ⊢ty[]≤[]∈[]-h (st-β₁ Γx⊢A∈K Γ⊢B∈J) = suc (⊢ty[]∈[]-h Γx⊢A∈K ⊔ ⊢ty[]∈[]-h Γ⊢B∈J)
  ⊢ty[]≤[]∈[]-h (st-β₂ Γx⊢A∈K Γ⊢B∈J) = suc (⊢ty[]∈[]-h Γx⊢A∈K ⊔ ⊢ty[]∈[]-h Γ⊢B∈J)
  ⊢ty[]≤[]∈[]-h (st-app Γ⊢A₁≤A₂ Γ⊢B₁==B₂) =
    suc (⊢ty[]≤[]∈[]-h Γ⊢A₁≤A₂ ⊔ ⊢ty[]==[]-h Γ⊢B₁==B₂)
  ⊢ty[]≤[]∈[]-h (st-bnd₁ Γ⊢τ∈S∙∙U) = suc (⊢ty[]∈[]-h Γ⊢τ∈S∙∙U)
  ⊢ty[]≤[]∈[]-h (st-bnd₂ Γ⊢τ∈S∙∙U) = suc (⊢ty[]∈[]-h Γ⊢τ∈S∙∙U)

  ⊢ty[]==[]-h : ∀{Γ A B K} → Γ ⊢ty A == B ∈ K → ℕ
  ⊢ty[]==[]-h (st-antisym Γ⊢A≤B Γ⊢B≤A) =
    suc (⊢ty[]≤[]∈[]-h Γ⊢A≤B ⊔ ⊢ty[]≤[]∈[]-h Γ⊢B≤A)

  ⊢tm[]∈[]-h : ∀{Γ t τ} → Γ ⊢tm t ∈ τ → ℕ
  ⊢tm[]∈[]-h (ty-var Γ[x]⊢>τ) = 1
  ⊢tm[]∈[]-h (ty-ℿ-intro Γx⊢e∈ρ) = suc (⊢tm[]∈[]-h Γx⊢e∈ρ)
  ⊢tm[]∈[]-h (ty-ℿ-elim Γ⊢f∈ℿτρ Γ⊢x∈τ) =
    suc (⊢tm[]∈[]-h Γ⊢f∈ℿτρ ⊔ ⊢tm[]∈[]-h Γ⊢x∈τ)
  ⊢tm[]∈[]-h (ty-new-intro Γ⊢ds∈τ) = ⊢defns[]∈[]-h Γ⊢ds∈τ
  ⊢tm[]∈[]-h (ty-new-elim Γ⊢x∈[ℓ∶τ]) = suc (⊢tm[]∈[]-h Γ⊢x∈[ℓ∶τ])
  ⊢tm[]∈[]-h (ty-let Γ⊢e₁∈τ Γx⊢e₂∈ρ) =
    suc (⊢tm[]∈[]-h Γ⊢e₁∈τ ⊔ ⊢tm[]∈[]-h Γx⊢e₂∈ρ)
  ⊢tm[]∈[]-h (ty-rec-intro Γ⊢x∈xτ) = suc (⊢tm[]∈[]-h Γ⊢x∈xτ)
  ⊢tm[]∈[]-h (ty-rec-elim Γ⊢x∈μτ) = suc (⊢tm[]∈[]-h Γ⊢x∈μτ)
  ⊢tm[]∈[]-h (ty-and-intro Γ⊢x∈τ₁ Γ⊢x∈τ₂) =
    suc (⊢tm[]∈[]-h Γ⊢x∈τ₁ ⊔ ⊢tm[]∈[]-h Γ⊢x∈τ₂)
  ⊢tm[]∈[]-h (ty-sub Γ⊢x∈S Γ⊢S≤U) = suc (⊢tm[]∈[]-h Γ⊢x∈S ⊔ ⊢ty[]≤[]∈[]-h Γ⊢S≤U)

  ⊢defn[]∈[]-h : ∀{Γ d τ} → Γ ⊢defn d ∈ τ → ℕ
  ⊢defn[]∈[]-h (ty-defn-type Γ⊢τ∈k) = suc (⊢ty[]∈[]-h Γ⊢τ∈k)
  ⊢defn[]∈[]-h (ty-defn-term Γ⊢e∈τ) = suc (⊢tm[]∈[]-h Γ⊢e∈τ)

  ⊢defns[]∈[]-h : ∀{Γ ds τ} → Γ ⊢defns ds ∈ τ → ℕ
  ⊢defns[]∈[]-h (ty-defns-one Γ⊢d∈τ) = suc (⊢defn[]∈[]-h Γ⊢d∈τ)
  ⊢defns[]∈[]-h (ty-defns-cons Γ⊢ds∈τ Γ⊢d∈D d∉ds) =
    suc (⊢defns[]∈[]-h Γ⊢ds∈τ ⊔ ⊢defn[]∈[]-h Γ⊢d∈D)

postulate
  narrowing-sk-kd : ∀ {Γ τ x J₁ J₂ K} →
    (p : Γ & x ~ Kd J₂ ⊢ty τ ∈ K) →
    Γ ⊢kd J₁ ≤ J₂ →
    Σ[ p' ∈ Γ & x ~ Kd J₁ ⊢ty τ ∈ K ] (⊢ty[]∈[]-h p ≡ ⊢ty[]∈[]-h p')

  narrowing-sk-tm : ∀ {Γ e x τ J K} →
    Γ ⊢tm e ∈ τ →
    (pf : Γ [ x ]⊢> Kd K) →
    Γ ⊢kd J ≤ K →
    replace Γ x (Kd J) pf ⊢tm e ∈ τ

{-
narrowing-sk-tm {Γ} {x = x} {J = J} (ty-ℿ-intro {y} {τ} {ρ} {e} e∈ρ) pf J≤K =
  ty-ℿ-intro narrow-e
  where
    narrow-e : replace Γ x (Kd J) pf & y ~ Ty τ ⊢tm openTerm y e ∈ openType y ρ
    narrow-e rewrite cong (λ t → t ⊢tm openTerm y e ∈ openType y ρ) (replace∘weaken pf) =
      {!
      narrowing-sk-tm e∈ρ (weaken Γ x y (Ty τ) pf) {! J≤K !}
      !}
narrowing-sk-tm (ty-ℿ-elim x∈τ₁⇒τ₂ z∈τ₁) pf J≤K =
  let narrow-x = narrowing-sk-tm x∈τ₁⇒τ₂ pf J≤K
      narrow-z = narrowing-sk-tm z∈τ₁ pf J≤K
   in
  ty-ℿ-elim narrow-x narrow-z
narrowing-sk-tm (ty-new-intro x) pf J≤K = {! !}
narrowing-sk-tm (ty-new-elim x∈[ℓ∶τ]) pf J≤K =
  let narrow-x = narrowing-sk-tm x∈[ℓ∶τ] pf J≤K
   in
  ty-new-elim narrow-x
narrowing-sk-tm (ty-let e∈τ x) pf J≤K = {! !}
narrowing-sk-tm (ty-rec-intro x∈τ[x]) pf J≤K = {! !}
narrowing-sk-tm (ty-rec-elim x∈μτ) pf J≤K = {! !}
narrowing-sk-tm (ty-and-intro x∈τ₁ x∈τ₂) pf J≤K =
  let narrow-x₁ = narrowing-sk-tm x∈τ₁ pf J≤K
      narrow-x₂ = narrowing-sk-tm x∈τ₂ pf J≤K
   in
  ty-and-intro narrow-x₁ narrow-x₂
narrowing-sk-tm (ty-sub e∈τ x) pf J≤K = {! !}
narrowing-sk-tm {Γ} {`(Free x)} {y} {τ} {J} {K} (ty-var Γ[x]⊢>τ) Γ[y]⊢>K J≤K
  with y ≟ x
... | no y≢x = ty-var (replace-spec-xy Γ y x (Kd J) (Ty τ) Γ[y]⊢>K Γ[x]⊢>τ y≢x)
... | yes y≡x rewrite y≡x =
  let K≡τ : Kd K ≡ Ty τ
      K≡τ = lookup-unique Γ[y]⊢>K Γ[x]⊢>τ

      K≢τ : Kd K ≢ Ty τ
      K≢τ = λ ()
   in
  ⊥-elim (K≢τ K≡τ)
-}


