open import OutsideIn.Prelude
open import OutsideIn.X
module OutsideIn.Instantiations.Simple where
  open import Data.Fin hiding (_+_; join)

  data Type ( n :  Set) : Set where
    funTy : Type n
    _·_   : Type n → Type n → Type n
    Var   : n → Type n

  private
    fmap-τ : ∀ {a b} → (a → b) → Type a → Type b
    fmap-τ f (funTy) = funTy
    fmap-τ f (x · y) = fmap-τ f x · fmap-τ f y
    fmap-τ f (Var v) = Var (f v)

    fmap-τ-id : ∀ {A : Set} {f : A → A} → isIdentity f → isIdentity (fmap-τ f)
    fmap-τ-id {f = f} isid {funTy} = refl
    fmap-τ-id {f = f} isid {α · β} = cong₂ _·_  (fmap-τ-id isid) (fmap-τ-id isid)
    fmap-τ-id {f = f} isid {Var  v} = cong Var isid
    fmap-τ-comp : {A B C : Set} {f : A → B} {g : B → C} {x : Type A}       
                → fmap-τ (g ∘ f) x ≡ fmap-τ g (fmap-τ f x)
    fmap-τ-comp {x = funTy} = refl
    fmap-τ-comp {x = α · β} = cong₂ _·_ fmap-τ-comp fmap-τ-comp
    fmap-τ-comp {x = Var v}  = cong Var refl
    join-τ :{a : Set} → Type (Type a)  → Type a
    join-τ (funTy) = funTy
    join-τ (x · y) = join-τ x · join-τ y
    join-τ (Var v) = v
    left-id : ∀ {a}{τ : Type a} → join-τ (fmap-τ Var τ) ≡ τ
    left-id {_}{funTy} = refl
    left-id {_}{α · β} = cong₂ _·_  (left-id {τ = α}) (left-id {τ = β})
    left-id {_}{Var  v} = refl
    assoc : ∀{A B C}{a : B → Type C}{b : A → Type B}{τ : Type A}
          → join-τ (fmap-τ a (join-τ (fmap-τ b τ)))
          ≡ join-τ (fmap-τ (λ v' → join-τ (fmap-τ a (b v'))) τ)
    assoc {a = a}{b}{funTy} = refl
    assoc {a = a}{b}{α · β} = cong₂ _·_  (assoc {τ = α}) (assoc {τ = β})
    assoc {a = a}{b}{Var  v} = refl

  type-is-functor : Functor Type
  type-is-functor = record { map = fmap-τ
                           ; identity = fmap-τ-id
                           ; composite = fmap-τ-comp
                           }
  type-is-monad : Monad Type 
  type-is-monad = record { is-functor = type-is-functor
                         ; point = Var
                         ; join = join-τ
                         ; is-left-ident  = left-id 
                         ; is-right-ident = refl 
                         ; >=>-assoc = λ {_}{_}{_}{_}{_}{_}{c}{v} → assoc {τ = c v}
                         }

  data SConstraint (x : Set) : Set where
     _∼_ : Type x → Type x → SConstraint x
     _∧′_ : SConstraint x → SConstraint x → SConstraint x
     ε : SConstraint x 

  sconstraint-is-functor : Functor SConstraint 
  sconstraint-is-functor = record { map = s-map; identity = s-ident; composite = s-comp }
     where open Functor (type-is-functor)
           s-map : {A B : Set} → (A → B) → SConstraint A → SConstraint B
           s-map f (ε) = ε
           s-map f (a ∼ b) = map f a ∼ map f b
           s-map f (a ∧′ b) = s-map f a ∧′ s-map f b
           s-ident : {A : Set} {f : A → A} → isIdentity f → isIdentity (s-map f)
           s-ident isid {ε} = refl
           s-ident isid {a ∼ b} = cong₂ _∼_ (identity isid) (identity isid) 
           s-ident isid {a ∧′ b} = cong₂ _∧′_ (s-ident isid) (s-ident isid) 
           s-comp : {A B C : Set} {f : A → B} {g : B → C} {x : SConstraint A} 
                  → s-map (g ∘ f) x ≡ s-map g (s-map f x)
           s-comp {x = ε} = refl
           s-comp {x = a ∼ b} = cong₂ _∼_ composite composite
           s-comp {x = a ∧′ b} = cong₂ _∧′_ s-comp s-comp

  _⟶_ : ∀ {n} → Type n → Type n → Type n
  a ⟶ b = (funTy · a) · b

  instance
    types : Types
    types = record { Type = Type
                   ; type-is-monad = type-is-monad
                   ; funType = _⟶_; appType = _·_
                   }

  data SVar (tc : Set)(n : ℕ) : Set where
    base : tc → SVar tc n
    unification : Fin n → SVar tc n

  thick : ∀ {n} → (x y : Fin (suc n)) → Ⓢ (Fin n)
  thick zero zero = zero
  thick zero (suc y) = suc y
  thick {zero } (suc ()) _ 
  thick {suc _} (suc x)  zero = suc zero
  thick {suc _} (suc x) (suc y) with thick x y
  ... | zero = zero
  ... | suc n = suc (suc n)

  thick-ident : ∀ {n} → (x : Fin (suc n)) → thick x x ≡ zero
  thick-ident zero = refl
  thick-ident (suc zero) = refl
  thick-ident (suc (suc x)) rewrite thick-ident (suc x) = refl

  check : ∀ {tc}{n} → Fin (suc n) → Type (SVar tc (suc n)) → Ⓢ (Type (SVar tc n))
  check x (funTy) = suc funTy
  check x (Var (base v)) = suc (Var (base v))
  check x (Var (unification n)) = map (Var ∘ unification) (thick x n) 
   where open Functor (Monad.is-functor Ⓢ-is-monad)
  check x (a · b) = check x a >>= λ a′ →
                     check x b >>= λ b′ → 
                      unit (a′ · b′)
   where open Monad (Ⓢ-is-monad)

  data AList (tc : Set) : ℕ → ℕ → Set where
    anil : ∀ {n} → AList tc n n
    _asnoc_/_ : ∀ {m n} → AList tc m n → Type (SVar tc m) → Fin (suc m) → AList tc (suc m) n


  _∃asnoc_/_ : ∀ {tc}{m} (a : ∃ (AList tc m)) (t' : Type (SVar tc m)) (x : Fin (suc m)) 
             →  ∃ (AList tc (suc m))
  (n , σ) ∃asnoc t' / x = n , σ asnoc t' / x

  _for_ : ∀{tc}{n} → (Type (SVar tc n)) → Fin (suc n)
        → SVar tc (suc n) → Type (SVar tc n)
  (t′ for x) (base y) = Var (base y)
  (t′ for x) (unification y) with thick x y
  ... | suc y′ = Var (unification y′)
  ... | zero   = t′

  check-implies-for-invariant : ∀ {tc}{n}{t : Type (SVar tc n)}{x : Fin (suc n)}{s : Type (SVar tc (suc n))}{s' : Type (SVar tc n)}
    → check x s ≡ suc s'
    → let open Monad (type-is-monad) in
       s >>= (t for x) ≡ s'
  check-implies-for-invariant {s = funTy} refl = refl
  check-implies-for-invariant {x = x} {s = s · s₁} prf with check x s with inspect (check x) s with check x s₁ with inspect (check x) s₁
  check-implies-for-invariant {t = t} {x = x} {s · s₁} refl | suc s' | iC prf' | suc s₁' | iC prf₁'
    = cong₂ _·_ (check-implies-for-invariant {t = t} {x = x} {s = s} prf') (check-implies-for-invariant {t = t} {x = x} {s = s₁} prf₁')
  check-implies-for-invariant {s = Var (base x)} refl = refl
  check-implies-for-invariant {x = x} {s = Var (unification x')} prf with thick x x'
  check-implies-for-invariant {x = x} {Var (unification x')} refl | suc x'' = refl

  sub : ∀ {m n}{tc} → AList tc m n → SVar tc m → Type (SVar tc n)  
  sub anil = Var
  sub (σ asnoc t / x) = sub σ >=> (t for x)
    where open Monad (type-is-monad)

  flexFlex : ∀ {tc}{m} (x y : Fin m) → ∃ (AList tc m)    
  flexFlex {_}{suc m} x y with thick x y
  ...              | suc y′ = m , anil asnoc Var (unification y′) / x
  ...              | zero   = suc m , anil
  flexFlex {_}{zero} () _

  flexRigid : ∀ {tc}{m} (x : Fin m) (t : Type (SVar tc m)) -> Ⓢ (∃(AList tc m))
  flexRigid {_}{suc m} x t with check x t
  ...                      | suc t′ = suc (m , anil asnoc t′ / x)
  ...                      | zero   = zero
  flexRigid {_}{zero} () _

  amgu : ∀{tc}{m} → (Eq tc) → (s t : Type (SVar tc m)) → ∃ (AList tc m) → Ⓢ (∃ (AList tc m))
  amgu eq (funTy) (funTy) acc = suc acc 
  amgu eq (Var (base a)) (Var (base b)) acc with Eq.eq eq a b
  ... | true = suc acc 
  ... | false = zero 
  amgu eq (Var (base a)) (funTy) acc = zero 
  amgu eq (funTy) (Var (base b)) acc = zero 
  amgu eq (funTy) (a · b) acc = zero
  amgu eq (Var (base _)) (a · b) acc = zero
  amgu eq (a · b) (funTy) acc = zero
  amgu eq (a · b) (Var (base _)) acc = zero
  amgu eq (a · b) (a′ · b′) acc = amgu eq a a′ acc >>= amgu eq b b′ 
     where open Monad (Ⓢ-is-monad)
  amgu eq (Var (unification x)) (Var (unification y)) (m , anil) = suc (flexFlex x y)
  amgu eq (Var (unification x)) t (m , anil) = flexRigid x t 
  amgu eq t (Var (unification x)) (m , anil) = flexRigid x t 
  amgu eq s t (n , σ asnoc r / z) = Ⓢ-f.map (λ σ → σ ∃asnoc r / z) (amgu eq (s >>= (r for z)) 
                                                                             (t >>= (r for z)) 
                                                                             (n , σ)) 
    where module Ⓢ-f = Functor (Monad.is-functor Ⓢ-is-monad)
          open Monad (type-is-monad)

  data Alist-extend : ∀{tc}{m n n'} → AList tc m n' → AList tc m n → Set where
    alist-extend-base : ∀{tc}{m n}{al' : AList tc m n} → Alist-extend al' anil
    alist-extend-asnoc : ∀{tc}{m n n'}{t : Type (SVar tc m)}{x : Fin (suc m)}
      {al' : AList tc m n}{al : AList tc m n'}
      → Alist-extend al' al
      → Alist-extend (al' asnoc t / x) (al asnoc t / x)

  alist-extend-id : ∀{tc}{m n}{al : AList tc m n} → Alist-extend al al
  alist-extend-id {al = anil} = alist-extend-base
  alist-extend-id {al = al asnoc x / x₁} = alist-extend-asnoc alist-extend-id


  alist-extend-trans : ∀{tc}{m n n' n''}{al : AList tc m n}{al' : AList tc m n'}{al'' : AList tc m n''}
    → Alist-extend al' al''
    → Alist-extend al'' al
    → Alist-extend al' al
  alist-extend-trans alist-extend-base alist-extend-base = alist-extend-base
  alist-extend-trans (alist-extend-asnoc al'-extend-al'') alist-extend-base = alist-extend-base
  alist-extend-trans (alist-extend-asnoc al'-extend-al'') (alist-extend-asnoc al''-extend-al)
    = alist-extend-asnoc (alist-extend-trans al'-extend-al'' al''-extend-al)

  alist-invariant : ∀{tc}{m n n'}{s t : Type (SVar tc m)} {al : AList tc m n} {al' : AList tc m n'}
    → Alist-extend al' al
    → let open Monad (type-is-monad) in s >>= (sub al) ≡ t >>= (sub al)
    → s >>= (sub al') ≡ t >>= (sub al')
  alist-invariant {s = s} {t = t} alist-extend-base prf
    rewrite left-id {τ = s} rewrite left-id {τ = t} rewrite prf = refl
  alist-invariant {s = s'} {t = t'} (alist-extend-asnoc {t = t} {x = x} {al' = al'} {al = al} IH) prf = begin
    s' >>= (sub al' >=> (t for x))
      ≡⟨ >>=->=>commute {s = s'} ⟩ ((s' >>= (t for x)) >>= sub al')
      ≡⟨ alist-invariant {s = s' >>= (t for x)} {t = t' >>= (t for x)} IH †
        ⟩ (t' >>= (t for x)) >>= sub al'
      ≡⟨ sym (>>=->=>commute {s = t'}) ⟩ t' >>= (sub al' >=> (t for x)) ∎
    where open ≡-Reasoning
          open Monad (type-is-monad)
          † : ((s' >>= (t for x)) >>= sub al) ≡ ((t' >>= (t for x)) >>= sub al)
          † = begin
            ((s' >>= (t for x)) >>= sub al)
              ≡⟨ sym (>>=->=>commute {s = s'}) ⟩ (s' >>= (sub al >=> (t for x)))
              ≡⟨ prf ⟩ (t' >>= (sub al >=> (t for x)))
              ≡⟨ >>=->=>commute {s = t'} ⟩ ((t' >>= (t for x)) >>= sub al)
            ∎

  amgu-extend : ∀{tc}{m}{n n'}{al al'}{s t : Type (SVar tc m)}{eq}
    → amgu eq s t (n , al) ≡ suc (n' , al')
    → Alist-extend al' al
  amgu-extend {s = funTy} {t = funTy} refl = alist-extend-id
  amgu-extend {al = anil} {s = funTy} {t = Var (unification x)} prf = alist-extend-base
  amgu-extend {n = n} {al = al asnoc x₁ / x₂} {s = funTy} {t = Var (unification x)} {eq} prf with thick x₂ x
  amgu-extend {n = n} {al = al asnoc x₁ / x₂} {s = funTy} {t = Var (unification x)} {eq} prf | suc x' with † (n , al) with inspect † (n , al)
    where open Monad (type-is-monad)
          † = amgu eq funTy (Var (unification x'))
  amgu-extend {n = n} {_} {al asnoc x₁ / x₂} {_} {funTy} {Var (unification x)} {eq} refl | suc x' | suc (n'' , al'') | iC prf'
    = alist-extend-asnoc (amgu-extend {s = funTy} {t = Var (unification x')} prf')
  amgu-extend {n = n} {_} {al asnoc x₁ / x₂} {_} {funTy} {Var (unification x)} {eq} () | suc x' | zero | iC prf'
  amgu-extend {n = n} {al = al asnoc x₁ / x₂} {s = funTy} {t = Var (unification x)} {eq} prf | zero with † (n , al) with inspect † (n , al)
    where open Monad (type-is-monad)
          † = amgu eq funTy x₁
  amgu-extend {n = n} {_} {al asnoc x₁ / x₂} {_} {funTy} {Var (unification x)} {eq} refl | zero | suc (n'' , al'') | iC prf'
    = alist-extend-asnoc (amgu-extend {s = funTy} {t = x₁} prf')
  amgu-extend {n = n} {al = al} {s = s · s₁} {t = t · t₁} {eq} prf with † (n , al) with inspect † (n , al)
    where open Monad (type-is-monad)
          † = amgu eq s t
  ... | suc (n'' , al'') | iC prf'
    = alist-extend-trans (amgu-extend {s = s₁} {t = t₁} prf) (amgu-extend {s = s} {t = t} prf')
  amgu-extend {n = _} {al = anil} {s = s · s₁} {t = Var (unification x)} {eq} prf = alist-extend-base
  amgu-extend {n = n} {al = al asnoc x₁ / x₂} {s = s · s₁} {t = Var (unification x)} {eq} prf with thick x₂ x
  ... | suc x' with † (n , al) with inspect † (n , al)
    where open Monad (type-is-monad)
          † = amgu eq ((s >>= (x₁ for x₂)) · (s₁ >>= (x₁ for x₂))) (Var (unification x'))
  amgu-extend {n = n} {_} {al asnoc x₁ / x₂} {_} {s · s₁} {Var (unification x)} {eq} refl | suc x' | suc (n'' , al'') | iC prf'
    = alist-extend-asnoc (amgu-extend {s = (s >>= (x₁ for x₂)) · (s₁ >>= (x₁ for x₂))} {t = Var (unification x')} prf')
    where open Monad (type-is-monad)
  amgu-extend {n = n} {al = al asnoc x₁ / x₂} {s = s · s₁} {t = Var (unification x)} {eq} prf | zero with † (n , al) with inspect † (n , al)
    where open Monad (type-is-monad)
          † = amgu eq ((s >>= (x₁ for x₂)) · (s₁ >>= (x₁ for x₂))) x₁
  amgu-extend {n = n} {_} {al asnoc x₁ / x₂} {_} {s · s₁} {Var (unification x)} {eq} refl | zero | suc (n'' , al'') | iC prf'
    = alist-extend-asnoc (amgu-extend {s = (s >>= (x₁ for x₂)) · (s₁ >>= (x₁ for x₂))} {t = x₁} prf')
    where open Monad (type-is-monad)
  amgu-extend {al = anil} {s = Var (unification x)} {t = funTy} prf = alist-extend-base
  amgu-extend {n = n} {al = al asnoc x₁ / x₂} {s = Var (unification x)} {t = funTy} {eq} prf with † (n , al) with inspect † (n , al)
    where open Monad (type-is-monad)
          † = amgu eq (Var (unification x) >>= (x₁ for x₂)) (funTy >>= (x₁ for x₂))
  amgu-extend {n = n} {_} {al asnoc x₁ / x₂} {_} {Var (unification x)} {funTy} {eq} refl | suc (n'' , al'') | iC prf'
    = alist-extend-asnoc (amgu-extend {s = (x₁ for x₂) (unification x)} {t = funTy} prf')
  amgu-extend {n = _} {al = anil} {s = Var (unification x)} {t = t · t₁} {eq} prf = alist-extend-base
  amgu-extend {n = n} {al = al asnoc x₁ / x₂} {s = Var (unification x)} {t = t · t₁} {eq} prf with † (n , al) with inspect † (n , al)
    where open Monad (type-is-monad)
          † = amgu eq (Var (unification x) >>= (x₁ for x₂)) ((t · t₁) >>= (x₁ for x₂))
  amgu-extend {n = n} {_} {al asnoc x₁ / x₂} {_} {Var (unification x)} {t · t₁} {eq} refl | suc (n'' , al'') | iC prf'
    = alist-extend-asnoc (amgu-extend {s = (x₁ for x₂) (unification x)} {t = (t >>= (x₁ for x₂)) · (t₁ >>= (x₁ for x₂))} prf')
    where open Monad (type-is-monad)
  amgu-extend {n = n} {al = al} {s = Var (base x)} {t = Var (base x₁)} {eq} prf with Eq.eq eq x x₁
  amgu-extend {n = n} {al = al} {_} {Var (base x)} {Var (base x₁)} {eq} refl | true = alist-extend-id
  amgu-extend {n = n} {al = al} {_} {Var (base x)} {Var (base x₁)} {eq} () | false
  amgu-extend {n = _} {al = anil} {s = Var (base x)} {t = Var (unification x₁)} {eq} prf = alist-extend-base
  amgu-extend {n = n} {al = al asnoc x₂ / x₃} {s = Var (base x)} {t = Var (unification x₁)} {eq} prf with † (n , al) with inspect † (n , al)
    where open Monad (type-is-monad)
          † = amgu eq (Var (base x) >>= (x₂ for x₃)) (Var (unification x₁) >>= (x₂ for x₃))
  amgu-extend {n = n} {_} {al asnoc x₂ / x₃} {_} {Var (base x)} {Var (unification x₁)} {eq} refl | suc (n'' , al'') | iC prf'
    = alist-extend-asnoc (amgu-extend {s = Var (base x)} {t = (x₂ for x₃) (unification x₁)} prf')
  amgu-extend {n = _} {al = anil} {s = Var (unification x)} {t = Var (base x₁)} {eq} prf = alist-extend-base
  amgu-extend {n = n} {al = al asnoc x₂ / x₃} {s = Var (unification x)} {t = Var (base x₁)} {eq} prf with † (n , al) with inspect † (n , al)
    where open Monad (type-is-monad)
          † = amgu eq (Var (unification x) >>= (x₂ for x₃)) (Var (base x₁) >>= (x₂ for x₃))
  amgu-extend {n = n} {_} {al asnoc x₂ / x₃} {_} {Var (unification x)} {Var (base x₁)} {eq} refl | suc (n'' , al'') | iC prf'
    = alist-extend-asnoc (amgu-extend {s = (x₂ for x₃) (unification x)} {t = Var (base x₁)} prf')
  amgu-extend {n = _} {al = anil} {s = Var (unification x)} {t = Var (unification x₁)} {eq} prf = alist-extend-base
  amgu-extend {n = n} {al = al asnoc x₂ / x₃} {s = Var (unification x)} {t = Var (unification x₁)} {eq} prf with † (n , al) with inspect † (n , al)
    where open Monad (type-is-monad)
          † = amgu eq (Var (unification x) >>= (x₂ for x₃)) (Var (unification x₁) >>= (x₂ for x₃))
  amgu-extend {n = n} {_} {al asnoc x₂ / x₃} {_} {Var (unification x)} {Var (unification x₁)} {eq} refl | suc (n'' , al'') | iC prf'
    = alist-extend-asnoc (amgu-extend {s = (x₂ for x₃) (unification x)} {t = (x₂ for x₃) (unification x₁)} prf')

  amgu-weak : ∀{tc}{m}{n n'}{al al'}{eq}{s t s' t' : Type (SVar tc m)}
    → let open Monad (type-is-monad) in amgu eq s' t' (n , al) ≡ suc (n' , al')
    → s >>= (sub al) ≡ t >>= (sub al)
    → s >>= (sub al') ≡ t >>= (sub al')
  amgu-weak {s = s} {t = t} {s' = s'} {t' = t'} = (alist-invariant {s = s} {t = t}) ∘ (amgu-extend {s = s'} {t = t'})
    where open Monad (type-is-monad)

  amgu-sound : ∀{tc}{m}{n}{al}{acc} → (eq : Eq tc) (s t : Type (SVar tc m))
    → amgu eq s t acc ≡ suc (n , al)
    → let open Monad (type-is-monad) in s >>= (sub al) ≡ t >>= (sub al)
  amgu-sound {m = m} {acc = acc} eq s t prf with amgu eq s t acc with inspect (amgu eq s t) acc
  amgu-sound {m = m} {acc = acc} eq funTy funTy prf | suc (n' , al') | iC prf' = refl
  amgu-sound {m = .(suc m₁)} {acc = suc m₁ , anil} eq funTy (Var (unification x)) refl | suc (.m₁ , .(anil asnoc funTy / x)) | iC refl rewrite thick-ident x = refl
  amgu-sound {m = .(suc _)} {acc = m₁ , (σ asnoc t / x')} eq funTy (Var (unification x)) refl | suc (n' , al') | iC prf' with † (m₁ , σ) with inspect † (m₁ , σ)
    where open Monad (type-is-monad)
          † = amgu eq (funTy >>= (t for x')) (Var (unification x) >>= (t for x'))
  amgu-sound {_} {.(suc _)} {.n''} {.(al'' asnoc t / x')} {m₁ , (σ asnoc t / x')} eq funTy (Var (unification x)) refl | suc (.n'' , .(al'' asnoc t / x')) | iC refl | suc (n'' , al'') | iC prf''
    rewrite amgu-sound eq funTy ((t for x') (unification x)) prf'' = refl
  amgu-sound {m = m} {acc = acc} eq (s · s₁) (t · t₁) refl | suc (n' , al') | iC prf' with † acc with inspect † acc
    where open Monad (type-is-monad)
          † = amgu eq s t
  ... | suc (n'' , al'') | iC prf'' rewrite amgu-sound eq s₁ t₁ prf'
    = cong
      (λ x → x · (t₁ >>= (sub al')))
      (alist-invariant {s = s} {t = t} {al = al''}
        (amgu-extend {s = s₁} {t = t₁} {eq = eq} prf')
        (amgu-sound eq s t prf''))
    where open Monad (type-is-monad)
  amgu-sound {m = .(suc m')} {acc = suc m' , anil} eq (s · s₁) (Var (unification x)) refl | suc (n' , al') | iC prf' with check x (s · s₁) with inspect (check x) (s · s₁)
  amgu-sound {_} {.(suc m')} {.m'} {.(anil asnoc rlt / x)} {suc m' , anil} eq (s · s₁) (Var (unification x)) refl | suc (.m' , .(anil asnoc rlt / x)) | iC refl | suc rlt | iC prf''
    rewrite thick-ident x = begin
      (s >>= (Var >=> (rlt for x))) · (s₁ >>= (Var >=> (rlt for x)))
      ≡⟨ cong₂ _·_ (>>=->=>commute {s = s}) (>>=->=>commute {s = s₁}) ⟩
        ((s >>= (rlt for x)) >>= Var) · ((s₁ >>= (rlt for x)) >>= Var)
      ≡⟨ cong₂ _·_ left-id left-id ⟩
        (s >>= (rlt for x)) · (s₁ >>= (rlt for x))
      ≡⟨ check-implies-for-invariant {t = rlt} {x = x} {s = s · s₁} prf'' ⟩ rlt
      ≡⟨ sym left-id ⟩ rlt >>= Var
    ∎
    where open ≡-Reasoning
          open Monad (type-is-monad)
  amgu-sound {m = .(suc _)} {acc = m' , (snd asnoc x₁ / x₂)} eq (s · s₁) (Var (unification x)) refl | suc (n' , al') | iC prf' with † (m' , snd) with inspect † (m' , snd)
    where open Monad (type-is-monad)
          † = amgu eq ((s · s₁) >>= (x₁ for x₂)) (Var (unification x) >>= (x₁ for x₂))
  amgu-sound {_} {.(suc _)} {.n''} {.(al'' asnoc x₁ / x₂)} {m' , (σ asnoc x₁ / x₂)} eq (s · s₁) (Var (unification x)) refl | suc (.n'' , .(al'' asnoc x₁ / x₂)) | iC refl | suc (n'' , al'') | iC prf''
    = {!!}
    where open Monad (type-is-monad)
  amgu-sound {m = m} {acc = acc} eq (Var x) t prf | suc (n' , al') | iC prf' = {!!}


  mgu : ∀{tc}{m}(eq : Eq tc)(s t : Type (SVar tc m)) → Ⓢ (∃ (AList tc m))
  mgu {m = m} eq s t = amgu eq s t (m , anil)


  prf : ∀ {m n} → m + suc n ≡ suc m + n
  prf {zero} = refl
  prf {suc n} = cong suc (prf {n})
  prf₂ : ∀ {m} →  m + zero ≡ m
  prf₂ {zero} = refl
  prf₂ {suc n} = cong suc prf₂

  svar-iso₁′ : ∀{m n}{tc} → SVar tc n ⨁ m → SVar tc (m + n) 
  svar-iso₁′ {zero} x = x
  svar-iso₁′ {suc m}{n}{tc} v = subst (SVar tc) (prf {m}{n}) (svar-iso₁′ {m}{suc n} (pm-f.map ind v)) 
   where module pm-f = Functor (Monad.is-functor (PlusN-is-monad {m}))
         ind : ∀{tc}{m} → Ⓢ (SVar tc m) → SVar tc (suc m)
         ind zero = unification zero
         ind (suc n) with n
         ... | base v = base v
         ... | unification x = unification (suc x)


  svar-iso₂′ : ∀{m}{tc} → Fin m → tc ⨁ m 
  svar-iso₂′ {zero} () 
  svar-iso₂′ {suc n} zero = pn-m.unit zero 
   where module pn-m = Monad (PlusN-is-monad {n})
  svar-iso₂′ {suc n} (suc v) = pm-f.map suc (svar-iso₂′ {n} v)
   where module pm-f = Functor (Monad.is-functor (PlusN-is-monad {n}))

  svar-iso₁ : ∀{m}{tc} → tc ⨁ m → SVar tc m
  svar-iso₁ {m}{tc} v = subst (SVar tc) prf₂ (svar-iso₁′ {m}{zero}{tc} (pm-f.map base v))
   where module pm-f = Functor (Monad.is-functor (PlusN-is-monad {m}))

  svar-iso₂ : ∀{m}{tc} → SVar tc m → tc ⨁ m 
  svar-iso₂ {m}{tc} (base v) = pm-m.unit v
   where module pm-m = Monad (PlusN-is-monad {m})
  svar-iso₂ {m}{tc} (unification v) = svar-iso₂′ v

  
  open Functor (Monad.is-functor type-is-monad) using () renaming (map to τ-map)

  mgu′ : ∀{tc}{m}(eq : Eq tc)(s t : Type (tc ⨁ m)) → Ⓢ (∃ (λ n → tc ⨁ m → Type (tc ⨁ n)))
  mgu′ {tc}{m} eq s t with mgu {tc}{m} eq (τ-map svar-iso₁ s) (τ-map svar-iso₁ t)
  ... | zero = zero
  ... | suc (n , al) = suc (n , τ-map svar-iso₂ ∘ sub al ∘ svar-iso₁)


  data SConstraintShape (x : Set) : Shape → Set where
     _∼_ : Type x → Type x → SConstraintShape x Nullary
     ε : SConstraintShape x Nullary
     _∧′_ : ∀ {a b} → SConstraintShape x a → SConstraintShape x b → SConstraintShape x (Binary a b)
 

  applySubst : ∀ {a b}{s} → (a → Type b) → SConstraintShape a s → SConstraintShape b s
  applySubst f (a ∼ b) = (a >>= f) ∼ (b >>= f)
    where open Monad (type-is-monad)
  applySubst f (a ∧′ b) = applySubst f a ∧′ applySubst f b
  applySubst f (ε) = ε




  constraint-types : ∀{a b} → (Type a → Type b) → (SConstraint a → SConstraint b)  
  constraint-types f ε = ε 
  constraint-types f (a ∧′ b) = constraint-types f a ∧′ constraint-types f b
  constraint-types f (a ∼ b) = f a ∼ f b

  applySubst′ : ∀ {a b} → (a → Type b) → SConstraint a  → SConstraint b 
  applySubst′ f Qc = constraint-types (λ a → (a >>= f)) Qc
    where open Monad (type-is-monad)

  data AxiomScheme (n : Set) : Set where
    ax : AxiomScheme n

  coerceAxioms : ∀ {a b} → AxiomScheme a → AxiomScheme b
  coerceAxioms ax = ax

  coerceId : ∀ {x} → isIdentity (coerceAxioms {x} {x})
  coerceId {_}{ax} = refl


  instance
    axiom-schemes : AxiomSchemes
    axiom-schemes = record { AxiomScheme = AxiomScheme
                           ; axiomscheme-types = λ f → coerceAxioms
                           ; axiomscheme-is-functor = record { map = λ f → coerceAxioms; identity = λ f → coerceId; composite = λ { {x = ax} → refl }}
                           }

  is-ε : ∀ {m} (x : SConstraint m) → Dec (x ≡ ε)
  is-ε ε = yes refl
  is-ε (a ∧′ b) = no (λ ())  
  is-ε (a ∼ b) = no (λ ())  

  instance
    qconstraints : QConstraints
    qconstraints = record { QConstraint = SConstraint
                          ; qconstraint-is-functor = sconstraint-is-functor
                          ; constraint-types = constraint-types
                          ; _∼_ = _∼_; _∧_ = _∧′_; ε = ε; is-ε = is-ε
                          }
  qc-substitute-unit : ∀{a} {Qc : QConstraints.QConstraint qconstraints a} → QConstraints.qc-substitute qconstraints (Type.Var) Qc ≡ Qc
  qc-substitute-unit {Qc = x ∼ x₁} rewrite left-id {τ = x} rewrite left-id {τ = x₁} = refl
  qc-substitute-unit {Qc = Qc ∧′ Qc₁} rewrite qc-substitute-unit {Qc = Qc} rewrite qc-substitute-unit {Qc = Qc₁} = refl
  qc-substitute-unit {Qc = ε} = refl



  open Monad (type-is-monad) hiding (_>=>_)
  open Functor (type-is-functor)
  data _,_⊩_ {n : Set}(Q : AxiomScheme n) : SConstraint n → SConstraint n → Set where
    ent-taut  : ∀ {q} → Q , q ⊩ ε
    ent-refl  : ∀ {q} → Q , q  ⊩ q
    ent-sym  : ∀ {q q′} → Q , (q ∧′ q′)  ⊩ (q′ ∧′ q)
    ent-proj  : ∀ {q q′} → Q , (q ∧′ q′)  ⊩ q
    ent-trans : ∀ {q₁ q₂ q₃} → Q , q₁ ⊩ q₂ → Q , q₂ ⊩ q₃ → Q , q₁ ⊩ q₃
    ent-typeq-refl : ∀ {q}{τ} → Q , q ⊩ (τ ∼ τ)
    ent-typeq-sym : ∀ {q}{τ₁ τ₂} → Q , q ⊩ (τ₁ ∼ τ₂) → Q , q ⊩ (τ₂ ∼ τ₁)
    ent-typeq-trans : ∀ {q}{τ₁ τ₂ τ₃} → Q , q ⊩ (τ₁ ∼ τ₂) → Q , q ⊩ (τ₂ ∼ τ₃) → Q , q ⊩ (τ₁ ∼ τ₃)
    ent-conj : ∀ {q q₁ q₂} → Q , q ⊩ q₁ → Q , q ⊩ q₂ → Q , q ⊩ (q₁ ∧′ q₂)

  ent-subst : ∀ {a b}{θ : a → Type b}{Q : AxiomScheme a}{q₁ q₂ : SConstraint a}
    → Q , q₁ ⊩ q₂
    → coerceAxioms Q , applySubst′ θ q₁ ⊩ applySubst′ θ q₂
  ent-subst ent-taut = ent-taut
  ent-subst ent-refl = ent-refl
  ent-subst ent-sym = ent-sym
  ent-subst ent-proj = ent-proj
  ent-subst (ent-trans a b) = ent-trans (ent-subst a) (ent-subst b)
  ent-subst (ent-typeq-refl) = ent-typeq-refl
  ent-subst (ent-typeq-sym a) = ent-typeq-sym (ent-subst a)
  ent-subst (ent-typeq-trans a b) = ent-typeq-trans (ent-subst a) (ent-subst b)
  ent-subst (ent-conj a b) = ent-conj (ent-subst a) (ent-subst b)

  ent-typeq-subst : ∀ {a b}{Q : AxiomScheme a}{q : SConstraint a}{τ₁ τ₂ : Type a}{θ : a → Type b} 
                  → Q , q ⊩ (τ₁ ∼ τ₂) → coerceAxioms Q , applySubst′ θ q
                                      ⊩ ((join ∘ map θ) τ₁ ∼ (join ∘ map θ) τ₂)
  ent-typeq-subst ent-refl = ent-refl
  ent-typeq-subst ent-proj = ent-proj
  ent-typeq-subst (ent-trans a b) = ent-trans (ent-subst a) (ent-typeq-subst b)
  ent-typeq-subst (ent-typeq-refl) = ent-typeq-refl
  ent-typeq-subst (ent-typeq-sym a) = ent-typeq-sym (ent-typeq-subst a)
  ent-typeq-subst (ent-typeq-trans a b) = ent-typeq-trans (ent-typeq-subst a) (ent-typeq-subst b)



  shapify : ∀ {a} → SConstraint a → ∃ (SConstraintShape a)
  shapify (a ∼ b) = Nullary , a ∼ b
  shapify (a ∧′ b) with shapify a | shapify b
  ... | r₁ , a′ | r₂ , b′ = Binary r₁ r₂ , a′ ∧′ b′
  shapify (ε) = Nullary , ε
  



  instance 
    entailment : Entailment
    entailment = record { _,_⊩_ = _,_⊩_
                        ; ent-refl = ent-refl
                        ; ent-trans = ent-trans
                        ; ent-subst = ent-subst
                        ; ent-typeq-refl = ent-typeq-refl
                        ; ent-typeq-sym = ent-typeq-sym
                        ; ent-typeq-trans = ent-typeq-trans
                        ; ent-typeq-subst = ent-typeq-subst
                        ; ent-conj = ent-conj
                        }


  open SimplificationPrelude ⦃ types ⦄ ⦃ axiom-schemes ⦄ ⦃ qconstraints ⦄ ⦃ entailment ⦄

  _contract-∧'_ : ∀ {x} → (Q Q' : SConstraint x) → SConstraint x
  Q contract-∧' Q' with is-ε Q with is-ε Q'
  ... | false because _ | yes refl = Q
  ... | yes refl | _ because _ = Q'
  ... | false because _ | false because _ = Q ∧′ Q'

  contract-preserve : ∀ {x} → {Q : AxiomScheme x} (Qc Qc' Qw Qw' : SConstraint x)
    → Q , (Qc ∧′ Qc') ⊩ (Qw ∧′ Qw') → Q , (Qc contract-∧' Qc') ⊩ (Qw ∧′ Qw')
  contract-preserve Qc Qc' Qw Qw' Qent with is-ε Qc with is-ε Qc'
  ... | false because _ | false because _ = Qent
  ... | false because _ | yes refl = ent-trans (ent-conj ent-refl ent-taut) Qent
  ... | yes refl | does₂ because _ = ent-trans (ent-conj ent-taut ent-refl) Qent


  constraint : ∀{s}{tc}{m} → Eq tc → SConstraintShape (tc ⨁ m) s → SimplifierResult tc m
  constraint {Unary _} _ ()
  constraint {Nullary}{m = m} _ ε = m , ε , solved ε Var
  constraint {Nullary}{tc}{m} eq (a ∼ b) = convert (mgu′ {tc}{m} eq a b)
   where 
    convert : Ⓢ (∃ (λ n → tc ⨁ m → Type (tc ⨁ n))) →  SimplifierResult tc m
    convert (suc (n , θ)) = n , ε , solved ε θ
    convert zero = m , (a ∼ b) , solved _ Var
  constraint {Binary r₁ r₂}{tc}{m} eq (a ∧′ b) =
    case (constraint {r₁}{tc}{m} eq a) of λ { (n , Qr , solved _ θ) →
      case (constraint {r₂}{tc}{n} eq (applySubst θ b)) of λ { (n′ , Qr′ , solved _ θ′) →
        n′ , Qr′ contract-∧' (applySubst′ θ′ Qr) , solved _ (θ′ >=> θ)
      }
    }
    where open import Function using (case_of_)
          open Monad (type-is-monad)


  
  simplifier : {x : Set} → Eq x → (n : ℕ) → AxiomScheme x → SConstraint x 
                         → SConstraint (x ⨁ n) → SimplifierResult x n
  simplifier {x} eq n _ con₁ con₂ with is-ε con₁
  ... | yes refl = case shapify con₂ of λ { (r , v) → constraint {r}{x}{n} eq v }
    where open import Function using (case_of_)
  ... | no _ = n , con₂ , solved _ Var


  applySubst-composition : ∀ {x} {n} {m} {m'}
                              {θ : x ⨁ n → Type (x ⨁ m)}
                              {θ' : x ⨁ m → Type (x ⨁ m')}
                              {s} {Qs : SConstraintShape (x ⨁ n) s} →
                              let open Monad (type-is-monad) in
                                (applySubst θ' ∘ applySubst θ) Qs ≡
                                applySubst (θ' >=> θ) Qs
  applySubst-composition {θ = θ} {θ' = θ'} {Qs = x ∼ x'}
    rewrite assoc {a = θ'} {b = θ} {τ = x}
    rewrite assoc {a = θ'} {b = θ} {τ = x'} = refl
  applySubst-composition {θ = θ} {θ' = θ'} {Qs = ε} = refl
  applySubst-composition {x}{n}{m}{m'}{θ}{θ'}{Qs = Qs ∧′ Qs'}
    rewrite applySubst-composition {x}{n}{m}{m'}{θ}{θ'}{_}{Qs}
    rewrite applySubst-composition {x}{n}{m}{m'}{θ}{θ'}{_}{Qs'} = refl

  applySubst-commute' : ∀ {x} {n} {eq : Eq x} {m} {m'}
                          {θ' : x ⨁ m → Type (x ⨁ m')}
                          {θ : x ⨁ n → Type (x ⨁ m)}
                          {Qc : SConstraint (x ⨁ n)} →
                        constraint {m = m'} eq (
                          (applySubst θ' ∘ applySubst θ) (proj₂ (shapify Qc))
                        ) ≡
                        constraint eq (
                          applySubst θ' (proj₂ (shapify (applySubst′ θ Qc)))
                        )
  applySubst-commute' {Qc = x ∼ x₁} = refl
  applySubst-commute' {x}{n}{eq}{m}{m'}{θ'}{θ}{Qc = Qc ∧′ Qc'}
    rewrite applySubst-commute' {x}{n}{eq}{m}{m'}{θ'}{θ}{Qc}
    with constraint {m = m'} eq (applySubst θ' (proj₂ (shapify (applySubst′ θ Qc))))
  ... | (n' , Qr' , solved _ θ'')
    rewrite applySubst-composition {x}{m}{m'}{n'}{θ'}{θ''}{_}{proj₂(shapify (applySubst′ θ Qc'))}
    rewrite applySubst-composition {x}{m}{m'}{n'}{θ'}{θ''}{_}{(applySubst θ (proj₂ (shapify Qc')))}
    rewrite applySubst-commute' {x}{n}{eq}{m}{n'}{Monad._>=>_ type-is-monad θ'' θ'}{θ}{Qc'}
    = refl
  applySubst-commute' {Qc = ε} = refl

  applySubst-unit : ∀ {x} {s} {Qs : SConstraintShape x s} → applySubst Var Qs ≡ Qs
  applySubst-unit {Qs = x ∼ x'}
    rewrite left-id {τ = x} rewrite left-id {τ = x'} = refl
  applySubst-unit {Qs = ε} = refl
  applySubst-unit {Qs = Qs ∧′ Qs'}
    rewrite applySubst-unit {Qs = Qs} rewrite applySubst-unit {Qs = Qs'} = refl

  applySubst-commute : ∀ {x} {n} {eq : Eq x} {m} {θ : x ⨁ n → Type (x ⨁ m)}
                          {Qc : SConstraint (x ⨁ n)} →
                        constraint {m = m} eq (applySubst θ (proj₂ (shapify Qc))) ≡
                        constraint eq (proj₂ (shapify (applySubst′ θ Qc)))
  applySubst-commute {x}{n}{eq}{m}{θ}{Qc} = begin
    constraint eq (applySubst θ (proj₂ (shapify Qc))) ≡⟨ † ⟩
    constraint eq (applySubst Var (applySubst θ (proj₂ (shapify Qc)))) ≡⟨ applySubst-commute' {x}{n}{eq}{m}{m}{Var}{θ}{Qc} ⟩
    constraint eq (applySubst Var (proj₂ (shapify (applySubst′ θ Qc)))) ≡⟨ †' ⟩
    constraint eq (proj₂ (shapify (applySubst′ θ Qc))) ∎
    where open ≡-Reasoning
          †' : constraint {m = m} eq (applySubst Var (proj₂ (shapify (applySubst′ θ Qc))))
            ≡ constraint eq (proj₂ (shapify (applySubst′ θ Qc)))
          †' rewrite applySubst-unit {Qs = proj₂ (shapify (applySubst′ θ Qc))} = refl
          † : constraint {m = m} eq (applySubst θ (proj₂ (shapify Qc)))
            ≡ constraint eq (applySubst Var (applySubst θ (proj₂ (shapify Qc))))
          † rewrite applySubst-unit {Qs = applySubst θ (proj₂ (shapify Qc))} = refl

  simplifier-sound : {x : Set} {n : ℕ} {eq : Eq x}
                     (Q : AxiomScheme x) (Qg : SConstraint x)
                     (Qw : SConstraint (x ⨁ n))
                     {s : Shape}
                     → s ≡ proj₁ (shapify Qw)
                     → IsSound Q Qg Qw (simplifier eq n Q Qg Qw)
  simplifier-sound {x} {n} {eq} Q Qg Qw _ with is-ε Qg
  ... | no _ rewrite qc-substitute-unit {Qc = Qw} = ent-trans ent-sym ent-proj
  simplifier-sound {x} {n} {eq} Q Qg (x₁ ∼ x₂) _
    | yes refl
    with simplifier eq n Q Qg (x₁ ∼ x₂)
    with inspect (simplifier eq n Q Qg) (x₁ ∼ x₂)
  ... | m , Qr , X.solved .Qr θ | iC prf
    with mgu′ {x}{n} eq x₁ x₂
  simplifier-sound {x} {.m} {eq} Q Qg (x₁ ∼ x₂) _
    | yes refl
    | m , (.x₁ ∼ .x₂) , X.solved .(x₁ ∼ x₂) .Var
    | iC refl
    | zero
    rewrite left-id {τ = x₁}
    rewrite left-id {τ = x₂}
    = ent-trans ent-sym ent-proj
  simplifier-sound {x} {n} {eq} Q Qg (x₁ ∼ x₂) _
    | yes refl
    | m , (Qr ∧′ Qr₁) , X.solved .(Qr ∧′ Qr₁) θ
    | iC ()
    | suc (m' , θ')
  simplifier-sound {x} {n} {eq} Q Qg (x₁ ∼ x₂) _
    | yes refl
    | m , (Qr ∧′ Qr₁) , X.solved .(Qr ∧′ Qr₁) θ
    | iC ()
    | zero
  simplifier-sound {x} {n} {eq} Q Qg (x₁ ∼ x₂) _
    | yes refl
    | m , ε , X.solved .ε θ
    | iC refl
    | suc (m₁ , θ₁) = {!!}
  simplifier-sound {x} {n} {eq} Q Qg (Qw ∧′ Qw') {Binary a b} shape-prf
    | yes refl
    with simplifier eq n Q Qg Qw
    with inspect (simplifier eq n Q Qg) Qw
    with simplifier-sound {x} {n} {eq} Q Qg Qw  {a}
  ... |  m' , Qr' , solved .Qr' θ' | iC prf' | Qw-sound
    with simplifier eq m' Q Qg (applySubst′ θ' Qw')
    with inspect (simplifier eq m' Q Qg) (applySubst′ θ' Qw')
    with simplifier-sound {x} {m'} {eq} Q Qg (applySubst′ θ' Qw') {b}
  simplifier-sound {x} {n} {eq} Q Qg (Qw ∧′ Qw') {Binary .(proj₁ (shapify Qw)) .(proj₁ (shapify Qw'))} refl
    | yes refl
    | m' , Qr' , X.solved .Qr' θ' | iC prf'
    | Qw-sound | m'' , Qr'' , X.solved .Qr'' θ'' | iC prf''
    | Qw'-sound
    rewrite applySubst-commute {x}{n}{eq}{m'}{θ'}{Qw'}
    rewrite prf' rewrite prf''
    = ent-trans
        ent-sym
        (ent-trans
          ent-proj
          (contract-preserve
            Qr''
            (applySubst′ θ'' Qr')
            _ _
            (ent-conj
              (ent-trans ent-sym
                (ent-trans ent-proj
                  (subst
                    (λ Q → (Q , applySubst′ θ'' Qr' ⊩ applySubst′ (θ'' >=> θ') Qw))
                    †''
                    (subst
                      (λ Qw →
                        (coerceAxioms
                          (coerceAxioms Q) , applySubst′ θ'' Qr' ⊩ Qw
                        )
                      )
                      (†' {Qw})
                      (ent-subst {θ = θ''}
                        (ent-trans
                          (ent-conj ent-taut ent-refl)
                          (Qw-sound refl)
                        )
                      )
                    )
                  )
                )
              )
              (ent-trans ent-proj
                (subst
                  (λ Qw → (coerceAxioms Q , Qr'' ⊩ Qw))
                  ((†' {Qw'}))
                  (ent-trans (ent-conj ent-taut ent-refl) (Qw'-sound († {Qw'})))
                )
              )
            )
          )
        )
    where open Monad(type-is-monad)
          † : ∀ {Qc} → proj₁ (shapify Qc) ≡ proj₁ (shapify (applySubst′ θ' Qc))
          † {x ∼ x₁} = refl
          † {Qc ∧′ Qc₁} rewrite † {Qc} rewrite † {Qc₁} = refl
          † {ε} = refl
          †' : ∀ {Qc} → applySubst′ θ'' (applySubst′ θ' Qc) ≡ applySubst′ (θ'' >=> θ') Qc
          †' {x ∼ x₁}
            rewrite assoc {a = θ''} {b = θ'} {τ = x₁}
            rewrite assoc {a = θ''} {b = θ'} {τ = x} = refl
          †' {Qc ∧′ Qc₁} rewrite †' {Qc} rewrite †' {Qc₁} = refl
          †' {ε} = refl
          †'' : ∀ {Q} → coerceAxioms {x ⨁ m'} {x ⨁ m''} (coerceAxioms Q) ≡ coerceAxioms Q
          †'' {ax} = refl
  simplifier-sound {x} {n} {eq} Q Qg ε _
    | yes refl
    with simplifier eq n Q Qg ε
    with inspect (simplifier eq n Q Qg) ε
  ... | m , ε , X.solved .ε θ | iC prf = ent-trans ent-sym ent-proj

  simplification : Simplification
  simplification = record {
    simplifier = simplifier;
    simplifier-sound = λ {x}{n}{eq} Q Qg Qw →
      let s , _ = shapify Qw in
      simplifier-sound {x}{n}{eq} Q Qg Qw {s} refl
    }

  Simple : (ℕ → Set) → X
  Simple dc = record { dc = dc
                     ; types = types
                     ; axiom-schemes = axiom-schemes
                     ; qconstraints = qconstraints
                     ; entailment = entailment
                     ; simplification = simplification
                     }


