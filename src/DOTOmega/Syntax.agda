open import Level renaming (zero to lzero; suc to lsuc) hiding (Lift)
open import Relation.Binary using (DecSetoid)

-- TODO: We basically never actually use the Setoid structure of labels
-- anywhere (we can use [PropositionalEquality] basically everywhere).
module DOTOmega.Syntax
    (TypeL : DecSetoid lzero lzero)
    (TermL : DecSetoid lzero lzero)
  where

open import Data.Nat
open import Data.Fin
open import Data.Product
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality
open import Induction.WellFounded
open import Function.Base using (id)

open import Induction.Extensions

TypeLabel = DecSetoid.Carrier TypeL
TermLabel = DecSetoid.Carrier TermL
_≈Ty_ = DecSetoid._≈_ TypeL
_≈Tm_ = DecSetoid._≈_ TermL

infix 19 typ_∶_
infix 20 _∙∙_
infix 21 _∧_

-- Core syntax

mutual
  data Kind (n : ℕ) : Set where
    _∙∙_ : Type n → Type n → Kind n     -- interval kinds
    ℿ : Kind n → Kind (suc n) → Kind n  -- type-level function kinds

  data Type (n : ℕ) : Set where
    ⊤ : Type n                          -- top
    ⊥ : Type n                          -- bottom
    [_] : Decl n → Type n               -- record
    _∧_ : Type n → Type n → Type n      -- intersection
    _∙_ : Fin n → TypeLabel → Type n    -- type selection
    μ : Type (suc n) → Type n           -- recursive types
    ℿ : Type n → Type (suc n) → Type n  -- dependent function
    ƛ : Kind n → Type (suc n) → Type n  -- type lambda
    ` : Fin n → Type n                  -- type variable
    _⊡_ : Type n → Type n → Type n      -- application

  data Decl (n : ℕ) : Set where
    typ_∶_ : TypeLabel → Kind n → Decl n
    val_∶_ : TermLabel → Type n → Decl n

pattern ✶ = ⊥ ∙∙ ⊤

mutual
  data Term (n : ℕ) : Set where
    ` : Fin n → Term n                            -- variables
    V : Val n → Term n                            -- values
    _∙_ : Fin n → TermLabel → Term n              -- field selection
    _⊡_ : Fin n → Fin n → Term n                  -- application
    let'_in'_ : Term n → Term (suc n) → Term n    -- let-binding
    lettype_in'_ : Type n → Term (suc n) → Term n -- type binding

  data Val (n : ℕ) : Set where
    new : Type (suc n) → List (Defn (suc n)) → Val n -- new object definitions
    ƛ : Type n → Term (suc n) → Val n                -- lambdas

  data Defn (n : ℕ) : Set where
    typ_='_ : TypeLabel → Type n → Defn n
    val_='_ : TermLabel → Term n → Defn n

-- Utility functions

data Label : Set where
  TyL : TypeLabel → Label
  TmL : TermLabel → Label

data defnMatchesType {n} : TypeLabel → Defn n → Set where
  dmty-lbl : ∀{A A' τ} → A ≈Ty A' → defnMatchesType {n} A' (typ A =' τ)

data defnMatchesTerm {n} : TermLabel → Defn n → Set where
  dmtm-lbl : ∀{ℓ ℓ' e} → ℓ ≈Tm ℓ' → defnMatchesTerm {n} ℓ' (val ℓ =' e)

_∈_ : ∀{n} → Defn n → List (Defn n) → Set
(typ A =' _) ∈ ds = Any (defnMatchesType A) ds
(val ℓ =' _) ∈ ds = Any (defnMatchesTerm ℓ) ds

_∉_ : ∀{n} → Defn n → List (Defn n) → Set
d ∉ ds = ¬ (d ∈ ds)

mutual
  weakenKind : ∀{n} → Kind n → Kind (suc n)
  weakenKind (τ₁ ∙∙ τ₂) = weakenType τ₁ ∙∙ weakenType τ₂
  weakenKind (ℿ J K) = ℿ (weakenKind J) (weakenKind K)

  weakenType : ∀{n} → Type n → Type (suc n)
  weakenType ⊤ = ⊤
  weakenType ⊥ = ⊥
  weakenType [ decl ] = [ weakenDecl decl ]
  weakenType (τ₁ ∧ τ₂) = weakenType τ₁ ∧ weakenType τ₂
  weakenType (x ∙ A) = suc x ∙ A
  weakenType (μ τ) = μ (weakenType τ)
  weakenType (ℿ τ ρ) = ℿ (weakenType τ) (weakenType ρ)
  weakenType (ƛ k τ) = ƛ (weakenKind k) (weakenType τ)
  weakenType (` x) = ` (suc x)
  weakenType (g ⊡ τ) = weakenType g ⊡ weakenType τ

  weakenDecl : ∀{n} → Decl n → Decl (suc n)
  weakenDecl (typ A ∶ k) = typ A ∶ weakenKind k
  weakenDecl (val ℓ ∶ τ) = val ℓ ∶ weakenType τ

  weakenTerm : ∀{n} → Term n → Term (suc n)
  weakenTerm (` x) = ` (suc x)
  weakenTerm (V vl) = V (weakenVal vl)
  weakenTerm (a ∙ b) = suc a ∙ b
  weakenTerm (a ⊡ b) = suc a ⊡ suc b
  weakenTerm (let' t1 in' t2) = let' (weakenTerm t1) in' (weakenTerm t2)
  weakenTerm (lettype τ in' t) = lettype (weakenType τ) in' (weakenTerm t)

  weakenVal : ∀{n} → Val n → Val (suc n)
  weakenVal (ƛ τ e) = ƛ (weakenType τ) (weakenTerm e)
  weakenVal (new τ defns) = new (weakenType τ) (mapf defns)
    where
      mapf : ∀{n} → List (Defn n) → List (Defn (suc n))
      mapf [] = []
      mapf (defn ∷ defns) = weakenDefn defn ∷ mapf defns

  weakenDefn : ∀{n} → Defn n → Defn (suc n)
  weakenDefn (typ A =' τ) = typ A =' (weakenType τ)
  weakenDefn (val ℓ =' e) = val ℓ =' (weakenTerm e)

{-
mutual
  _/Kind_ : (Var → Type) → Kind → Kind
  _/Kind_ f (A ∙∙ B) = _/Type_ f A ∙∙ _/Type_ f B
  _/Kind_ f (ℿ J K) = ℿ (_/Kind_ f J) (_/Kind_ f K)

  _/Type_ : (Var → Type) → Type → Type
  _/Type_ f ⊤ = ⊤
  _/Type_ f ⊥ = ⊥
  _/Type_ f [ decl ] = [ _/Decl_ f decl ]
  _/Type_ f (τ₁ ∧ τ₂) = _/Type_ f τ₁ ∧ _/Type_ f τ₂
  _/Type_ f (x ∙ A) = x ∙ A
  _/Type_ f (μ τ) = μ (_/Type_ f τ)
  _/Type_ f (ℿ τ ρ) = ℿ (_/Type_ f τ) (_/Type_ f ρ)
  _/Type_ f (ƛ k τ) = ƛ (_/Kind_ f k) (_/Type_ f τ)
  _/Type_ f (` x) = f x
  _/Type_ f (g ⊡ τ) = _/Type_ f g ⊡ _/Type_ f τ

  _/Decl_ : (Var → Type) → Decl → Decl
  _/Decl_ f (typ A ∶ k) = typ A ∶ _/Kind_ f k
  _/Decl_ f (val ℓ ∶ τ) = val ℓ ∶ _/Type_ f τ

  _/Term_ : (Var → Type) → Term → Term
  _/Term_ f (` x) = ` x
  _/Term_ f (V vl) = V (_/Val_ f vl)
  _/Term_ f (a ∙ b) = a ∙ b
  _/Term_ f (a ⊡ b) = a ⊡ b
  _/Term_ f (let' t1 in' t2) = let' (_/Term_ f t1) in' (_/Term_ f t2)
  _/Term_ f (lettype τ in' t) = lettype (_/Type_ f τ) in' (_/Term_ f t)

  _/Val_ : (Var → Type) → Val → Val
  _/Val_ f (ƛ τ e) = ƛ τ (_/Term_ f e)
  _/Val_ f (new τ defns) = new (_/Type_ f τ) (mapf defns)
    where
      mapf : List Defn → List Defn
      mapf [] = []
      mapf (defn ∷ defns) = _/Defn_ f defn ∷ mapf defns

  _/Defn_ : (Var → Type) → Defn → Defn
  _/Defn_ f (typ A =' τ) = typ A =' (_/Type_ f τ)
  _/Defn_ f (val ℓ =' e) = val ℓ =' (_/Term_ f e)

open Subst (record {lift = KindLift; var = `; subst = _/Kind_})
  using ()
  renaming
  ( openT to openKind
  ; closeT to closeKind
  ; wkT to wkKind
  ; shiftT to shiftKind
  ; renameT to renameKind
  ; bindT to bindKind
  )
  public

open Subst (record {lift = TermLift; var = `; subst = _/Term_})
  using ()
  renaming
  ( openT to openTerm
  ; closeT to closeTerm
  ; wkT to wkTerm
  ; shiftT to shiftTerm
  ; renameT to renameTerm
  ; bindT to bindTerm
  )
  public

open Subst (record {lift = TypeLift; var = `; subst = _/Type_})
  using ()
  renaming
  ( openT to openType
  ; closeT to closeType
  ; wkT to wkType
  ; shiftT to shiftType
  ; renameT to renameType
  ; bindT to bindType
  )
  public

open Subst (record {lift = DefnLift; var = `; subst = _/Defn_})
  using ()
  renaming
  ( openT to openDefn
  ; closeT to closeDefn
  ; wkT to wkDefn
  ; shiftT to shiftDefn
  ; renameT to renameDefn
  ; bindT to bindDefn
  )
  public

open Subst (record {lift = KindLift; var = id; subst = liftKind})
  using ()
  renaming (bindT to plugKind)
  public

open Subst (record {lift = TypeLift; var = id; subst = liftType})
  using ()
  renaming (bindT to plugType)
  public

open Subst (record {lift = DefnLift; var = id; subst = liftDefn})
  using ()
  renaming (bindT to plugDefn)
  public

open Subst (record {lift = TermLift; var = id; subst = liftTerm})
  using ()
  renaming (bindT to plugTerm)
  public
-}

{-
data KindShape : Set where
  Interval : KindShape
  Pi : KindShape → KindShape → KindShape

kd-shape : Kind → KindShape
kd-shape (S ∙∙ U) = Interval
kd-shape (ℿ J K) = Pi (kd-shape J) (kd-shape K)

liftKind-preserves-shape : ∀ (f : Var → Var) K →
  kd-shape (liftKind f K) ≡ kd-shape K
liftKind-preserves-shape f (S ∙∙ U) = refl
liftKind-preserves-shape f (ℿ J K) = begin
    kd-shape (liftKind f (ℿ J K))
  ≡⟨ refl ⟩
    kd-shape (ℿ (liftKind f J) (liftKind f K))
  ≡⟨ refl ⟩
    Pi (kd-shape (liftKind f J)) (kd-shape (liftKind f K))
  ≡⟨ cong
      (λ t → Pi t (kd-shape (liftKind f K)))
      (liftKind-preserves-shape f J) ⟩
    Pi (kd-shape J) (kd-shape (liftKind f K))
  ≡⟨ cong (Pi (kd-shape J)) (liftKind-preserves-shape f K) ⟩
    Pi (kd-shape J) (kd-shape K)
  ≡⟨ refl ⟩
    kd-shape (ℿ J K)
  ∎
  where
    open ≡-Reasoning

unwrap-Pi-shape : ∀ {J K sJ sK} → kd-shape (ℿ J K) ≡ Pi sJ sK →
  kd-shape J ≡ sJ × kd-shape K ≡ sK
unwrap-Pi-shape {J} {K} {sJ} {sK} eq = split sJ sK (kd-shape J) (kd-shape K) eq
  where
    split : ∀ sJ sK sJ' sK' → Pi sJ' sK' ≡ Pi sJ sK → sJ' ≡ sJ × sK' ≡ sK
    split sJ sK .sJ .sK refl = refl , refl

infix 19 _<kd_

-- TODO: is this still true?
-- This measure is primarily used for the logical relation for type-level
-- normalization, which doesn't need to recurse into the type expressions
-- themselves. Because of that, we can just count [S ∙∙ U] as the base.
kd-size : Kind → ℕ
kd-size (S ∙∙ U) = 1
kd-size (ℿ J K) = suc (kd-size J + kd-size K)

_<kd_ : Kind → Kind → Set
J <kd K = kd-size J < kd-size K

<kd-wf : ∀ K → Acc _<kd_ K
<kd-wf = accMeasure kd-size

<kd-ℿ₁ : ∀ J K → J <kd ℿ J K
<kd-ℿ₁ J K = s≤s (m≤m+n (kd-size J) (kd-size K))

<kd-ℿ₂ : ∀ J K → K <kd ℿ J K
<kd-ℿ₂ J K = s≤s (m≤n+m (kd-size K) (kd-size J))

liftKind-preserves-size : ∀ (f : Var → Var) K →
  kd-size (liftKind f K) ≡ kd-size K
liftKind-preserves-size f (A ∙∙ B) = refl
liftKind-preserves-size f (ℿ J K) = begin
    kd-size (liftKind f (ℿ J K))
  ≡⟨ refl ⟩
    kd-size (ℿ (liftKind f J) (liftKind f K))
  ≡⟨ refl ⟩
    suc (kd-size (liftKind f J) + kd-size (liftKind f K))
  ≡⟨ cong
      (λ t → suc (t + kd-size (liftKind f K)))
      (liftKind-preserves-size f J)
   ⟩
    suc (kd-size J + kd-size (liftKind f K))
  ≡⟨ cong
      (λ t → suc (kd-size J + t))
      (liftKind-preserves-size f K)
   ⟩
    suc (kd-size J + kd-size K)
  ≡⟨ refl ⟩
    kd-size (ℿ J K)
  ∎
  where
    open ≡-Reasoning

liftKind-preserves-<₁ : ∀ J K (f : Var → Var) →
  J <kd K → liftKind f J <kd K
liftKind-preserves-<₁ J K f J<K rewrite liftKind-preserves-size f J = J<K

<kd-ℿ-open : ∀ x J K → openKind x K <kd ℿ J K
<kd-ℿ-open x J K = liftKind-preserves-<₁ K (ℿ J K) (openVar x) (<kd-ℿ₂ J K)
-}
