module Krivine (Atom Const : Set) where

open import Data.Nat
open import Data.Sum
open import Data.Vec as Vec using (Vec; _∷_; [])


data Type : Set where
  atom : Atom → Type
  _⇒_  : Type → Type → Type


Basis : ℕ → Set
Basis = Vec Type

data Var : ∀ {n} → Basis n → Type → Set where
  vzero : ∀ {n} {Γ : Basis n} {τ}   → Var (τ ∷ Γ) τ
  vsuc  : ∀ {n} {Γ : Basis n} {σ τ} → Var Γ τ → Var (σ ∷ Γ) τ

data Term (Σ : Const → Type) {n} (Γ : Basis n) : Type → Set where
  app : ∀ {σ τ} → Term Σ Γ (σ ⇒ τ) → Term Σ Γ σ → Term Σ Γ τ
  lam : ∀ {σ τ} → Term Σ (σ ∷ Γ) τ → Term Σ Γ (σ ⇒ τ)
  var : ∀ {τ}   → Var Γ τ → Term Σ Γ τ


mutual
  data Subst (A : ∀ {n} (Γ : Basis n) → Type → Set) : ∀ {n₁} (Γ₁ : Basis n₁) {n₂} (Γ₂ : Basis n₂) → Set where
    comp  : ∀ {n₁} {Γ₁ : Basis n₁} {n₂} {Γ₂ : Basis n₂} {n₃} {Γ₃ : Basis n₃} → Subst A Γ₁ Γ₂ → Subst A Γ₂ Γ₃ → Subst A Γ₁ Γ₃
    cons  : ∀ {n₁} {Γ₁ : Basis n₁} {n₂} {Γ₂ : Basis n₂} {τ}                  → A Γ₂ τ → Subst A Γ₁ Γ₂ → Subst A (τ ∷ Γ₁) Γ₂
    id    : ∀ {n} {Γ : Basis n}                                              → Subst A Γ Γ
    lift  : ∀ {n₁} {Γ₁ : Basis n₁} {n₂} {Γ₂ : Basis n₂} {τ}                  → Subst A Γ₁ Γ₂ → Subst A (τ ∷ Γ₁) (τ ∷ Γ₂)
    shift : ∀ {n} {Γ : Basis n} {τ}                                          → Subst A Γ (τ ∷ Γ)

  data Thunk (A : ∀ {n} (Γ : Basis n) → Type → Set) {n} (Γ : Basis n) τ : Set where
    thunk : ∀ {n'} {Γ' : Basis n'} → A Γ' τ → Subst (Thunk A) Γ' Γ → Thunk A Γ τ

lookup : ∀ {A : ∀ {n} (Γ : Basis n) → Type → Set} → (∀ {n} {Γ : Basis n} {σ} → Var Γ σ → Thunk A Γ σ) → (∀ {n₁} {Γ₁ : Basis n₁} {n₂} {Γ₂ : Basis n₂} {τ}
       → Thunk A Γ₁ τ → Subst (Thunk A) Γ₁ Γ₂ → Thunk A Γ₂ τ) → ∀ {n₁} {Γ₁ : Basis n₁} {n₂} {Γ₂ : Basis n₂} {τ} → Var Γ₁ τ → Subst (Thunk A) Γ₁ Γ₂ → Thunk A Γ₂ τ
lookup {A} box under = lookup'
  where
    lookup' : ∀ {n₁} {Γ₁ : Basis n₁} {n₂} {Γ₂ : Basis n₂} {τ} → Var Γ₁ τ → Subst (Thunk A) Γ₁ Γ₂ → Thunk A Γ₂ τ
    lookup' v        (comp ρ σ) = under (lookup' v ρ) σ
    lookup' vzero    (cons x _) = x
    lookup' (vsuc v) (cons _ σ) = lookup' v σ
    lookup' v        id         = box v
    lookup' vzero    (lift _)   = box vzero
    lookup' (vsuc v) (lift σ)   = under (lookup' v σ) shift
    lookup' v        shift      = box (vsuc v)


boxvar : ∀ {Σ : Const → Type} {n} {Γ : Basis n} {τ} → Var Γ τ → Thunk (Term Σ) Γ τ
boxvar v = thunk (var v) id

close : ∀ {Σ : Const → Type} {n₁} {Γ₁ : Basis n₁} {n₂} {Γ₂ : Basis n₂} {τ} → Thunk (Term Σ) Γ₁ τ → Subst (Thunk (Term Σ)) Γ₁ Γ₂ → Thunk (Term Σ) Γ₂ τ
close (thunk t ρ) σ = thunk t (comp ρ σ)


mutual
  subst : ∀ {Σ : Const → Type} {n₁} {Γ₁ : Basis n₁} {n₂} {Γ₂ : Basis n₂} {τ} → Term Σ Γ₁ τ → Subst (Thunk (Term Σ)) Γ₁ Γ₂ → Term Σ Γ₂ τ
  subst (app s t) σ  = app (subst s σ) (subst t σ)
  subst (lam t)   σ  = lam (subst t (lift σ))
  subst (var v)   id = var v
  subst (var v)   σ  = force (lookup boxvar close v σ)

  force : ∀ {Σ : Const → Type} {n} {Γ : Basis n} {τ} → Thunk (Term Σ) Γ τ → Term Σ Γ τ
  force (thunk t ρ) = subst t ρ


data Context (A : ∀ {n} (Γ : Basis n) → Type → Set) : ∀ {n₁} (Γ₁ : Basis n₁) {n₂} (Γ₂ : Basis n₂) → Type → Type → Set where
  app₁ : ∀ {n₁} {Γ₁ : Basis n₁} {n₂} {Γ₂ : Basis n₂} {ρ σ τ} → Context A Γ₁ Γ₂ σ τ → A Γ₁ ρ → Context A Γ₁ Γ₂ (ρ ⇒ σ) τ
  app₂ : ∀ {n₁} {Γ₁ : Basis n₁} {n₂} {Γ₂ : Basis n₂} {ρ σ τ} → A Γ₁ (ρ ⇒ σ) → Context A Γ₁ Γ₂ σ τ → Context A Γ₁ Γ₂ ρ τ
  lam₁ : ∀ {n₁} {Γ₁ : Basis n₁} {n₂} {Γ₂ : Basis n₂} {ρ σ τ} → Context A Γ₁ Γ₂ (ρ ⇒ σ) τ → Context A (ρ ∷ Γ₁) Γ₂ σ τ
  top  : ∀ {n} {Γ : Basis n} {τ}                             → Context A Γ Γ τ τ

foldctx : ∀ {A : ∀ {n} (Γ : Basis n) → Type → Set} {Σ : Const → Type} {n₁} {Γ₁ : Basis n₁} {n₂} {Γ₂ : Basis n₂} {σ τ}
        → (∀ {n} {Γ : Basis n} {ρ} → A Γ ρ → Term Σ Γ ρ) → Term Σ Γ₁ σ → Context A Γ₁ Γ₂ σ τ → Term Σ Γ₂ τ
foldctx f z (app₁ ctx y) = foldctx f (app z (f y)) ctx
foldctx f z (app₂ x ctx) = foldctx f (app (f x) z) ctx
foldctx f z (lam₁ ctx)   = foldctx f (lam z)       ctx
foldctx _ z top          = z


data Head (Σ : Const → Type) {n} (Γ : Basis n) : Type → Set where
  var : ∀ {τ} → Var Γ τ → Head Σ Γ τ

data Spine (Σ : Const → Type) (A : (∀ {n} (Γ : Basis n) → Type → Set) → ∀ {n} (Γ : Basis n) → Type → Set) {n} (Γ : Basis n) τ : Set where
  spine : ∀ {n'} {Γ' : Basis n'} {σ} → Head Σ Γ' σ → Context (A (Term Σ)) Γ' Γ σ τ → Spine Σ A Γ τ

eval : ∀ {Σ : Const → Type} {n₁} {Γ₁ : Basis n₁} {n₂} {Γ₂ : Basis n₂} {σ τ} → Thunk (Term Σ) Γ₁ σ → Context (Thunk (Term Σ)) Γ₁ Γ₂ σ τ → Spine Σ Thunk Γ₂ τ
eval (thunk (app s t) σ)  ctx         = eval (thunk s σ) (app₁ ctx (thunk t σ))
eval (thunk (lam t)   σ) (app₁ ctx x) = eval (thunk t (cons x σ)) ctx
eval (thunk (lam t)   σ)  ctx         = eval (thunk t (lift σ)) (lam₁ ctx)
eval (thunk (var v)   id) ctx         = spine (var v) ctx
eval (thunk (var v)   σ)  ctx         = eval (lookup boxvar close v σ) ctx


data Subst' (A : ∀ {n} (Γ : Basis n) → Type → Set) : ∀ {n₁} (Γ₁ : Basis n₁) {n₂} (Γ₂ : Basis n₂) → Set where
  comp  : ∀ {n₁} {Γ₁ : Basis n₁} {n₂} {Γ₂ : Basis n₂} {n₃} {Γ₃ : Basis n₃} → Subst A Γ₁ Γ₂ → Subst' A Γ₂ Γ₃ → Subst' A Γ₁ Γ₃
  id    : ∀ {n} {Γ : Basis n}                                              → Subst' A Γ Γ

data Thunk' (A : ∀ {n} (Γ : Basis n) → Type → Set) {n} (Γ : Basis n) τ : Set where
  thunk : ∀ {n'} {Γ' : Basis n'} → A Γ' τ → Subst' (Thunk' A) Γ' Γ → Thunk' A Γ τ

data Machine (Σ : Const → Type) {n} (Γ : Basis n) τ : Set where
  machine : ∀ {n'} {Γ' : Basis n'} {σ} → Thunk' (Term Σ) Γ' σ → Context (Thunk' (Term Σ)) Γ' Γ σ τ → Machine Σ Γ τ

coerce : ∀ {A : ∀ {n} (Γ : Basis n) → Type → Set} {n₁} {Γ₁ : Basis n₁} {n₂} {Γ₂ : Basis n₂} → Subst' A Γ₁ Γ₂ → Subst A Γ₁ Γ₂
coerce (comp ρ σ) = comp ρ (coerce σ)
coerce id         = id

step : ∀ {Σ : Const → Type} {n} {Γ : Basis n} {τ} → Machine Σ Γ τ → Spine Σ Thunk' Γ τ ⊎ Machine Σ Γ τ
step (machine (thunk (var v)         (comp shift                σ)) ctx) = inj₂ (machine (thunk (var (vsuc v)) σ)                                    ctx)
step (machine (thunk (var vzero)     (comp (cons (thunk u π) _) σ)) ctx) = inj₂ (machine (thunk u              (comp (coerce π) σ))                  ctx)
step (machine (thunk (var vzero)     (comp (lift _)             σ)) ctx) = inj₂ (machine (thunk (var vzero)    σ)                                    ctx)
step (machine (thunk (var (vsuc v))  (comp (cons (thunk _ _) ρ) σ)) ctx) = inj₂ (machine (thunk (var v)        (comp ρ          σ))                  ctx)
step (machine (thunk (var (vsuc v))  (comp (lift ρ)             σ)) ctx) = inj₂ (machine (thunk (var v)        (comp ρ (comp shift σ)))              ctx)
step (machine (thunk t               (comp (comp π ρ)           σ)) ctx) = inj₂ (machine (thunk t              (comp π (comp ρ σ)))                  ctx)
step (machine (thunk t               (comp id                   σ)) ctx) = inj₂ (machine (thunk t              σ)                                    ctx)
step (machine (thunk t               σ)          (app₂ (thunk s ρ) ctx)) = inj₂ (machine (thunk s              ρ)                 (app₁ ctx (thunk t σ)))
step (machine (thunk (app s (var v)) σ)                             ctx) = inj₂ (machine (thunk (var v)        σ)                 (app₂ (thunk s σ) ctx))
step (machine (thunk (app s t)       σ)                             ctx) = inj₂ (machine (thunk s              σ)                 (app₁ ctx (thunk t σ)))
step (machine (thunk (lam t)         σ)                    (app₁ ctx x)) = inj₂ (machine (thunk t              (comp (cons x (coerce σ)) id))        ctx)
step (machine (thunk (lam t)         σ)                             ctx) = inj₂ (machine (thunk t              (comp (lift (coerce σ)) id))   (lam₁ ctx))
step (machine (thunk (var v)         id)                            ctx) = inj₁ (spine (var v) ctx)

reduce : ∀ {Σ : Const → Type} {n} {Γ : Basis n} {τ} → Machine Σ Γ τ → Spine Σ Thunk' Γ τ
reduce m with step m
...      | inj₁ x  = x
...      | inj₂ m' = reduce m'
