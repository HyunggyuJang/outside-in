module OutsideIn.Prelude where

  open import Data.Nat public
  open import Relation.Binary.PropositionalEquality public renaming ([_] to iC) hiding (Extensionality)
  open import Axiom.Extensionality.Propositional
  open import Relation.Nullary public
  open import Function public hiding (case_of_; _⟶_)


  cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
          (f : A → B → C → D) {x y u v x′ y′} → x ≡ y → u ≡ v → x′ ≡ y′ 
        → f x u x′ ≡ f y v y′
  cong₃ f refl refl refl = refl  

  cong₄ : ∀ {a b c d e} {A : Set a} {B : Set b} {C : Set c} {D : Set d} {E : Set e}
          (f : A → B → C → D → E) {x y u v x′ y′ u′ v′} → x ≡ y → u ≡ v → x′ ≡ y′ → u′ ≡ v′ 
        → f x u x′ u′ ≡ f y v y′ v′
  cong₄ f refl refl refl refl = refl     

  import Level

  postulate extensionality : Extensionality Level.zero Level.zero

  module Shapes where

    -- Used throughout to show structure preserving operations preserve structure, 
    -- in order to maintain structural recursion.
    data Shape : Set where
      Nullary : Shape
      Unary : Shape → Shape
      Binary : Shape → Shape → Shape



  module Functors where


    import Data.Vec as V 
    open V using (_∷_; Vec; [])

    isIdentity : ∀ {A} → (A → A) → Set
    isIdentity {A} f = ∀ {x} → f x ≡ x 

    id-is-id : ∀ {A} → isIdentity {A} id
    id-is-id = refl 
    record Functor (X : Set → Set) : Set₁ where
      field map : ∀ {A B} → (A → B) → X A → X B
      _<$>_ : ∀ {A B} → (A → B) → X A → X B
      _<$>_ = map
      field identity : ∀ {A : Set}{f : A → A} → isIdentity f → isIdentity (map f)
      field composite : ∀ {A B C : Set} {f : A → B} {g : B → C}
                      → {x : X A} → ( (g ∘ f) <$> x ≡ g <$> (f <$> x))




    Pointed :  (Set → Set) → Set₁
    Pointed X = ∀ {a} → a → X a

    id-is-functor : Functor id
    id-is-functor = record { map = id; identity = id; composite = refl }

 

    vec-is-functor : ∀ {n} → Functor (λ A → Vec A n)
    vec-is-functor {n} = record { map = V.map; identity = ident {n} ; composite = composite }
      where ident :  {n : ℕ}{A : Set} {f : A → A} → isIdentity f →{x : Vec A n} → V.map f x ≡ x
            ident isid {[]} = refl
            ident isid {x ∷ xs} = cong₂ _∷_ isid (ident isid)
            composite : {A B C : Set}{n : ℕ} {f : A → B} {g : B → C} {x : Vec A n}
                      → V.map (g ∘ f) x ≡ V.map g (V.map f x)
            composite {x = []} = refl
            composite {x = x ∷ xs} = cong₂ _∷_ refl composite
    private
      module F = Functor ⦃ ... ⦄


    combine-composite′ : {X Y : Set → Set}{A B C : Set} ⦃ F2 : Functor Y ⦄ 
                        {V : X (Y A)}{f : A → B}{g : B → C} 
                      → (f1map  : ∀ {a b} → (a → b) → (X a → X b))
                      → (f1comp :  f1map (F.map g ∘ F.map f) V
                                ≡  f1map (F.map g) (f1map (F.map f) V))
                      → f1map (F.map ⦃ F2 ⦄ (g ∘ f)) V 
                      ≡ f1map (F.map ⦃ F2 ⦄ g) (f1map (F.map ⦃ F2 ⦄ f) V)

    combine-composite′ ⦃ F2 ⦄ {V} f1map f1comp =
      trans (cong (λ t → f1map t V) (extensionality (λ x → F.composite))) f1comp

    combine-composite : {X Y : Set → Set}{A B C : Set} ⦃ F1 : Functor X ⦄ ⦃ F2 : Functor Y ⦄ 
                        {V : X (Y A)}{f : A → B}{g : B → C} 
                      → F.map ⦃ F1 ⦄ (F.map ⦃ F2 ⦄ (g ∘ f)) V 
                      ≡ F.map ⦃ F1 ⦄ (F.map ⦃ F2 ⦄ g) (F.map ⦃ F1 ⦄ (F.map ⦃ F2 ⦄ f) V)
    combine-composite {X}{Y} ⦃ F1 ⦄ ⦃ F2 ⦄ {V} = combine-composite′ {X}{Y} 
                                                                    (F.map ⦃ F1 ⦄) 
                                                                    (F.composite ⦃ F1 ⦄)
    infixr 6 _∘f_ 
    _∘f_ : {X Y : Set → Set} → ( F1 : Functor X )( F2 : Functor Y )
                                    → Functor (X ∘ Y)
    F1 ∘f F2 = record { map = F.map ⦃ F1 ⦄ ∘ F.map ⦃ F2 ⦄ 
                      ; composite = combine-composite ⦃ F1 ⦄ ⦃ F2 ⦄
                      ; identity = F.identity ⦃ F1 ⦄ ∘ F.identity ⦃ F2 ⦄
                      }

  module StupidEquality where
    open import Data.Bool public using (Bool; true; false) 
    -- This equality doesn't place any proof demands
    -- because we don't actually care what equality is used.
    -- This is just for the initial base of type variables, where the user provides
    -- their own type equality relation. We don't care if it says Int ∼ Bool - this just
    -- provides a way for users to get some equality information threaded through the 
    -- simplifier
    record Eq (X : Set): Set where
      field eq : X → X → Bool
      _∼_ = eq

  module Monads where
    open Functors
   
    record Monad (X : Set → Set) : Set₁ where
      field is-functor : Functor X 
      field point : Pointed X 
      field join : ∀ {a} → X (X a) → X a
      open Functor is-functor
      unit : ∀ {a} → a → X a
      unit = point
      _>>=_ : ∀ {a b} → X a → (a → X b) → X b
      _>>=_ a b = join (b <$> a)
      _>>_ : ∀ {a b} → X a → X b → X b
      _>>_ a b = a >>= λ _ → b 
      _>=>_ : ∀ {a b c : Set} → (b → X c) → (a → X b) → (a → X c)
      _>=>_ a b = λ v → b v >>= a 
      field is-left-ident : ∀ {a b}{x : a → X b}{v} → (point >=> x) v ≡ x v
      field is-right-ident : ∀ {a b}{x : a → X b}{v} → (x >=> point) v ≡ x v
      field >=>-assoc : ∀{p}{q}{r}{s}{a : r → X s}{b : q → X r} {c : p → X q}{v}
                      → (a >=> (b >=> c)) v ≡ ((a >=> b) >=> c) v

      abstract
        <$>-unit : ∀ {A B}{g : A → B}{x} → g <$> (unit x) ≡  unit (g x)
        <$>-unit {A}{B}{g}{x} = begin 
          g <$> (unit x)                         ≡⟨ sym (is-left-ident {x = _<$>_ g}) ⟩
          join (unit <$> (g <$> (unit x)))       ≡⟨ cong join (sym composite) ⟩
          join ((unit ∘ g) <$> (unit x))         ≡⟨ is-right-ident ⟩
          unit (g x)                             ∎
         where open ≡-Reasoning



      abstract
        <$>-bind : ∀ {A B C}{f : A → B}{g : B → X C}{x : X A} 
                 → (f <$> x) >>= g ≡ x >>= (λ z → g (f z))
        <$>-bind = cong join (sym (composite))
 
        natural-trans : ∀ {A B}{f : A → B}{x : X( X A)} → f <$> (join x) ≡ join ((_<$>_ f) <$> x)
        natural-trans {A}{B}{f}{x} = begin 
           f <$> (join x)                                  ≡⟨ sym (is-left-ident {x = _<$>_ f}) ⟩
           join (unit <$> (f <$> (join x)))                ≡⟨ † ⟩
           join (unit <$> (f <$> (join (id <$> x))))       ≡⟨ <$>-bind ⟩
           join ((λ v → unit (f v)) <$> (join (id <$> x))) ≡⟨ >=>-assoc { c = λ _ → x}{0} ⟩
           join ((λ x → join ((unit ∘ f) <$> x)) <$> x )   ≡⟨ sym (<$>-bind) ⟩
           ((_<$>_ (λ y → unit (f y))) <$> x ) >>= join    ≡⟨ <$>-bind ⟩
           x >>= (λ x → x >>= (λ y → unit (f y)))          ≡⟨ * ⟩
           join ((_<$>_ f) <$> x)                          ∎ 
          where open ≡-Reasoning
                † : join (unit <$> (f <$> (join x))) ≡ join (unit <$> (f <$> (join (id <$> x))))
                † = cong (λ t → join (unit <$> (f <$> join t))) (sym (identity id-is-id ))
                * : x >>= (λ x → x >>= (λ y → unit (f y))) ≡ join ((_<$>_ f) <$> x)
                * = cong (_>>=_ x) 
                         (extensionality (λ y → trans (sym <$>-bind) 
                                                      (is-left-ident {x = _<$>_ f}{v = y})))
        >>=->=>commute : ∀ {a b c}{f : a → X b}{g : b → X c}{s : X a} → s >>= (g >=> f) ≡ (s >>= f) >>= g
        >>=->=>commute {f = f}{g = g}{s = s} = begin
          s >>= (g >=> f)
            ≡⟨ refl ⟩ (λ _ → s) 0 >>= (g >=> f)
            ≡⟨ refl ⟩ ((g >=> f) >=> (λ _ → s)) 0
            ≡⟨ sym (>=>-assoc { c = λ _ → s }{0}) ⟩ (g >=> (f >=> (λ _ → s))) 0
            ≡⟨ refl ⟩ (f >=> (λ _ → s)) 0 >>= g
            ≡⟨ refl ⟩ ((λ _ → s) 0 >>= f) >>= g
            ≡⟨ refl ⟩ (s >>= f) >>= g ∎
          where open ≡-Reasoning

    id-is-monad : Monad id
    id-is-monad = record { is-functor = id-is-functor 
                         ; point = id 
                         ; join = id
                         ; >=>-assoc = refl
                         ; is-left-ident = refl
                         ; is-right-ident = refl
                         }

    record MonadHomomorphism {M₁ M₂ : Set → Set}(h : ∀ {x : Set} → M₁ x → M₂ x) 
                             ⦃ M₁-m : Monad M₁ ⦄ ⦃ M₂-m : Monad M₂ ⦄ : Set₁ where
      open Monad M₁-m using () renaming (unit to unit₁; join to join₁; is-functor to is-functor₁)
      open Monad M₂-m using () renaming (unit to unit₂; join to join₂; is-functor to is-functor₂)
      open Functor is-functor₁ using () renaming (map to map₁)
      open Functor is-functor₂ using () renaming (map to map₂)
      field h-return :  ∀ {A}{x : A} → h (unit₁ x) ≡ unit₂ x
      field h-fmap : {A B : Set} {f : A → B} {x : M₁ A}
                     → h (map₁ f x) ≡ map₂ f (h x)
      field h-join : ∀{τ}{x : M₁ (M₁ τ)} → h (join₁ x) ≡ join₂ (h (map₁ h x))

    record MonadTrans (X : (Set → Set) → Set → Set) : Set₁ where
      field produces-monad : ∀ {m} → Monad m → Monad (X m)
      field lift : ∀ {m}⦃ mm : Monad m ⦄{a} → m a → X m a
      field is-homomorphism : ∀ {m} → ⦃ mm : Monad m ⦄
                            → MonadHomomorphism {m} {X m} (lift {m}) ⦃ mm ⦄ ⦃ produces-monad mm ⦄

  module Ⓢ-Type where
    open Functors
    open Monads
    open StupidEquality
 
    data Ⓢ (τ : Set) : Set where
      suc : τ → Ⓢ τ
      zero : Ⓢ τ


    cata-Ⓢ : {a b : Set} → b → (a → b) → Ⓢ a → b
    cata-Ⓢ nil something zero = nil
    cata-Ⓢ nil something (suc n) = something n     

    sequence-Ⓢ : ∀ {m}{b} → ⦃ monad : Monad m ⦄ →  Ⓢ (m b) → m (Ⓢ b)
    sequence-Ⓢ ⦃ m ⦄ (suc n) = map suc n
      where open Functor (Monad.is-functor m)
    sequence-Ⓢ ⦃ m ⦄ zero = unit zero
      where open Monad (m)

    private
      fmap-Ⓢ : ∀ {a b} → (a → b) → Ⓢ a → Ⓢ b
      fmap-Ⓢ f zero = zero
      fmap-Ⓢ f (suc n) = suc (f n)
      abstract
        fmap-Ⓢ-id : ∀ {A} → {f : A → A} 
                   → isIdentity f → isIdentity (fmap-Ⓢ f)
        fmap-Ⓢ-id isid {zero} = refl
        fmap-Ⓢ-id isid {suc x} = cong suc isid

        fmap-Ⓢ-comp : ∀ {A B C : Set} {f : A → B} {g : B → C} → ∀ {x} 
                     → fmap-Ⓢ (g ∘ f) x ≡ fmap-Ⓢ g (fmap-Ⓢ f x)
        fmap-Ⓢ-comp {x = zero} = refl
        fmap-Ⓢ-comp {x = suc n} = refl

    Ⓢ-is-functor : Functor Ⓢ
    Ⓢ-is-functor = record { map = fmap-Ⓢ
                           ; identity = fmap-Ⓢ-id
                           ; composite = fmap-Ⓢ-comp
                           }


    Ⓢ-eq : ∀ {x} → Eq x → Eq (Ⓢ x)
    Eq.eq (Ⓢ-eq x) (suc x₁) (suc x₂) = x₁ ∼ x₂
      where open Eq x
    Eq.eq (Ⓢ-eq x) (suc x₁) zero = false
    Eq.eq (Ⓢ-eq x) zero (suc x₁) = false
    Eq.eq (Ⓢ-eq x) zero zero = true


    private
      join-Ⓢ : ∀ {x} → Ⓢ (Ⓢ x) → Ⓢ x
      join-Ⓢ (zero) = zero
      join-Ⓢ (suc τ) = τ
 
      test-join : ∀ {A B}{f : A → B}{x : Ⓢ( Ⓢ A)} 
                → fmap-Ⓢ f (join-Ⓢ x) ≡ join-Ⓢ (fmap-Ⓢ (fmap-Ⓢ f) x)
      test-join {x = zero} = refl
      test-join {x = suc n} = refl
   
    Ⓢ-is-monad : Monad Ⓢ 
    Ⓢ-is-monad = record { is-functor     = Ⓢ-is-functor
                         ; point          = suc
                         ; join           = join-Ⓢ
                         ; is-left-ident  = left-id
                         ; is-right-ident = refl
                         ; >=>-assoc        = λ { {c = c}{v} → assoc {τ = c v} }
                         }
        where 
          left-id : ∀ {τ : Set}{v : Ⓢ τ} → join-Ⓢ (fmap-Ⓢ suc v) ≡ v
          left-id {v = zero } = refl
          left-id {v = suc v} = refl
          assoc : ∀ {q r s : Set} {a : r → Ⓢ s} {b : q → Ⓢ r}{τ : Ⓢ q} 
                → join-Ⓢ (fmap-Ⓢ a (join-Ⓢ (fmap-Ⓢ b τ))) 
                ≡ join-Ⓢ (fmap-Ⓢ (λ v′ → join-Ⓢ (fmap-Ⓢ  a (b v′))) τ)
          assoc {τ = zero} = refl
          assoc {τ = suc v} = refl


     
    Ⓢ-Trans : (Set → Set) → Set → Set
    Ⓢ-Trans m x = m (Ⓢ x)

    private 
      lift : ∀ {m : Set → Set}⦃ mm : Monad m ⦄{x} → m x → m (Ⓢ x) 
      lift {m}⦃ mm ⦄{x} v = suc <$> v
        where open Monad mm
              open Functor is-functor

      module MonadProofs {m : Set → Set}⦃ mm : Monad m ⦄ where
        open Monad mm
        open Functor is-functor
        functor : Functor (Ⓢ-Trans m)
        functor = record { map = λ f v → (fmap-Ⓢ f) <$> v 
                         ; identity = λ p → identity (fmap-Ⓢ-id p)
                         ; composite = λ { {x = x} → trans (cong (λ t → t <$> x) 
                                                           (extensionality ext)) composite }
                         } 
          where ext : ∀ {A B C : Set} {f : A → B} {g : B → C} → (x' : Ⓢ A)
                    → fmap-Ⓢ (g ∘ f) x' ≡ (fmap-Ⓢ g ∘ fmap-Ⓢ f) x'
                ext (zero) = refl
                ext (suc n) = refl
                         
        module Trans = Functor functor
 
        private 
          cata-Ⓢ-u0 : ∀ {a b} → (a → m (Ⓢ b)) → Ⓢ a → m (Ⓢ b)
          cata-Ⓢ-u0 = cata-Ⓢ (unit zero)
        abstract
          right-id :  {a b : Set} {x : a → Ⓢ-Trans m b} {v : a} 
                   → Trans.map x (lift {m} (unit v)) >>= cata-Ⓢ-u0 id ≡ x v
          right-id {a}{b}{x}{v} = begin
            Trans.map x (suc <$> (unit v)) >>= cata-Ⓢ-u0 id ≡⟨ * ⟩
            (fmap-Ⓢ x <$> (unit (suc v))) >>= cata-Ⓢ-u0 id ≡⟨ † ⟩
            join (cata-Ⓢ-u0 id <$> (unit (suc (x v))))      ≡⟨ cong join <$>-unit ⟩
            join (unit (x v))                                ≡⟨ cong join (sym(identity id-is-id)) ⟩
            join (id <$> unit (x v))                         ≡⟨ is-right-ident {x = id} ⟩
            x v                                              ∎    
           where open ≡-Reasoning
                 * : Trans.map x (suc <$> (unit v)) >>= cata-Ⓢ-u0 id
                   ≡ (fmap-Ⓢ x <$> (unit (suc v))) >>= cata-Ⓢ-u0 id
                 * = cong (λ t → Trans.map x t >>= cata-Ⓢ-u0 id) <$>-unit
                 † : (fmap-Ⓢ x <$> (unit (suc v))) >>= cata-Ⓢ-u0 id
                   ≡ join (cata-Ⓢ-u0 id <$> (unit (suc (x v))))
                 † = cong (λ x → x >>= cata-Ⓢ-u0 id) <$>-unit

          left-id : {b : Set} {t : Ⓢ-Trans m b} 
                  → Trans.map (λ x' → lift {m} (unit x')) t >>= cata-Ⓢ-u0 id ≡ t
          left-id {b}{t} = trans <$>-bind (subst (λ q → t >>= q ≡ t) 
                                                 (sym (extensionality h≗unit)) 
                                                 (is-left-ident {x = λ _ → t} {v = 0}))
            where h : ∀ {A} → Ⓢ A → m (Ⓢ A)
                  h x = cata-Ⓢ-u0 id (fmap-Ⓢ (λ x' → suc <$> (unit x')) x)
                  h≗unit : ∀ {A} → h {A} ≗ unit
                  h≗unit zero = refl
                  h≗unit (suc y) = <$>-unit 
               


          assoc : ∀ {p q r s : Set}
                    {a : r → Ⓢ-Trans m s}{b : q → Ⓢ-Trans m r}{c : p → Ⓢ-Trans m q}
                    {v : p} 
                → Trans.map a (Trans.map b (c v) >>= cata-Ⓢ-u0 id) >>= cata-Ⓢ-u0 id
                ≡ Trans.map (λ v' → Trans.map a (b v') >>= cata-Ⓢ-u0 id) (c v) >>= cata-Ⓢ-u0 id
          assoc {p}{q}{r}{s}{a}{b}{c}{v} 
            = let
                †₀ = cata-fmap
                †₁ = cong (λ x → x >>= cata-Ⓢ (unit zero) a) cata-fmap                
                †₂ = >=>-assoc {c = λ _ → c v} {v = 0}
                †₃ = cong (_>>=_ (c v)) (extensionality ext)
                †₄ = cong (λ x → c v >>= cata-Ⓢ (unit zero) x) 
                          (extensionality (λ x → sym cata-fmap))
                †₅ = sym (cata-fmap)
              in begin 
                 Trans.map a (Trans.map b (c v) >>= cata-Ⓢ-u0 id) >>= cata-Ⓢ-u0 id ≡⟨ †₀ ⟩
                 ((fmap-Ⓢ b <$> c v) >>= cata-Ⓢ-u0 id) >>= cata-Ⓢ-u0 a            ≡⟨ †₁ ⟩
                 (c v >>= cata-Ⓢ-u0 b) >>= cata-Ⓢ-u0 a                             ≡⟨ †₂ ⟩
                 c v >>= (λ cv → cata-Ⓢ-u0 b cv >>= cata-Ⓢ-u0 a)                   ≡⟨ †₃ ⟩
                 c v >>= cata-Ⓢ-u0 (λ v' → b v' >>= cata-Ⓢ-u0 a)                   ≡⟨ †₄ ⟩
                 c v >>= cata-Ⓢ-u0 (λ v' → (fmap-Ⓢ a <$> b v') >>= cata-Ⓢ-u0 id)  ≡⟨ †₅ ⟩
                 Trans.map (λ v' → Trans.map a (b v') >>= cata-Ⓢ-u0 id) (c v) >>= cata-Ⓢ-u0 id ∎
           where open ≡-Reasoning
                 ext : (x : Ⓢ q) → cata-Ⓢ-u0 b x >>= cata-Ⓢ-u0 a 
                                  ≡ cata-Ⓢ-u0 (λ v' → b v' >>= cata-Ⓢ-u0 a) x
                 ext zero = begin 
                   join ((cata-Ⓢ-u0 a) <$> unit zero) ≡⟨ cong join <$>-unit ⟩
                   join (unit (unit zero))             ≡⟨ cong join (sym (identity id-is-id)) ⟩
                   join (id <$> unit (unit zero))      ≡⟨ is-right-ident ⟩
                   unit zero                           ∎
                 ext (suc n) = refl
                 cata-fmap : ∀{A B C}{a : A → B}{x : m (Ⓢ A)}{n : m C}{j : B → m C} 
                           → (fmap-Ⓢ a <$> x) >>= cata-Ⓢ n j ≡ x >>= cata-Ⓢ n (λ x → j ( a x))
                 cata-fmap {A}{B}{C}{a}{x}{n}{j} = trans <$>-bind 
                                                         (cong (_>>=_ x) (extensionality ext′))
                  where ext′ : (x' : Ⓢ A) → cata-Ⓢ n j (fmap-Ⓢ a x') 
                                           ≡ cata-Ⓢ n (λ x0 → j (a x0)) x'
                        ext′ zero = refl
                        ext′ (suc n) = refl
        produces-monad = record { point = λ x → lift ⦃ mm ⦄ (unit x)
                                ; is-functor = functor 
                                ; join = λ v → v >>= cata-Ⓢ (unit zero) id
                                ; is-left-ident = left-id 
                                ; is-right-ident = right-id 
                                ; >=>-assoc = λ {_}{_}{_}{_}{a}{b}{c}{v} 
                                            → assoc {a = a}{b}{c}{v}  
                                }


      module HomomorphismProofs {m : Set → Set}⦃ mm : Monad m ⦄ where
        open Monad mm
        open Functor is-functor
        open ≡-Reasoning  

        cata-Ⓢ-u0 : ∀ {a b} → (a → m (Ⓢ b)) → Ⓢ a → m (Ⓢ b)
        cata-Ⓢ-u0 = cata-Ⓢ (unit zero)

        fmap-p : ∀ {A B : Set} {f : A → B} {x} 
               → lift {m} (f <$> x) ≡ (fmap-Ⓢ f) <$> (lift {m} x)
        fmap-p {A}{B}{f}{x} =  begin 
          suc <$> (f <$> x)               ≡⟨ sym (composite) ⟩
          (λ t → suc (f t)) <$> x         ≡⟨ refl ⟩
          (λ t → fmap-Ⓢ f (suc t)) <$> x ≡⟨ composite ⟩
          (fmap-Ⓢ f) <$> (suc <$> x)     ∎

        join-p : ∀{τ}{x : m (m (τ))} 
               → suc <$> (join x) ≡ (suc <$> (_<$>_ suc <$> x)) >>= cata-Ⓢ-u0 id
        join-p {_}{x} = begin 
          suc <$> (join x)                                  ≡⟨ natural-trans ⟩ 
          join ((_<$>_ suc) <$> x)                          ≡⟨ refl ⟩
          x >>= (λ z → cata-Ⓢ-u0 id (suc (suc <$> z)))     ≡⟨ sym (<$>-bind) ⟩
          ((λ z → suc (suc <$> z)) <$> x) >>= cata-Ⓢ-u0 id ≡⟨ † ⟩
          (suc <$> (_<$>_ suc <$> x)) >>= cata-Ⓢ-u0 id     ∎ 
         where † = cong (λ x → x >>= cata-Ⓢ-u0 id) (composite)

        is-homomorphism : MonadHomomorphism (lift {m}) ⦃ mm ⦄ ⦃ MonadProofs.produces-monad ⦃ mm ⦄ ⦄
        is-homomorphism = record { h-return = refl 
                                 ; h-fmap = fmap-p
                                 ; h-join = join-p
                                 }
     
    Ⓢ-Trans-is-trans : MonadTrans (Ⓢ-Trans)
    Ⓢ-Trans-is-trans = record { produces-monad = λ mm → MonadProofs.produces-monad ⦃ mm ⦄
                               ; lift = λ{m} → lift {m}
                               ; is-homomorphism = λ ⦃ mm ⦄ → HomomorphismProofs.is-homomorphism ⦃ mm ⦄
                               }
   
  module PlusN-Type where

    open Ⓢ-Type
    open Monads
    open Functors
    open StupidEquality

    PlusN : (n : ℕ) → Set → Set
    PlusN zero = id
    PlusN (suc n) = Ⓢ-Trans (PlusN n)

    
    PlusN-eq : ∀ {n}{x} → Eq x → Eq (PlusN n x)
    PlusN-eq {zero} eq = eq
    PlusN-eq {suc n} eq = PlusN-eq {n} (Ⓢ-eq eq)

    PlusN-is-monad : ∀ {n} → Monad (PlusN n)
    PlusN-is-monad {zero} = id-is-monad
    PlusN-is-monad {suc n} = MonadTrans.produces-monad Ⓢ-Trans-is-trans (PlusN-is-monad {n})

    _⨁_ = flip PlusN

    sequence-PlusN : ∀ {m}{n}{b} → ⦃ monad : Monad m ⦄ → (m b) ⨁ n → m (b ⨁ n)
    sequence-PlusN {n = zero} x = x
    sequence-PlusN {n = suc n} ⦃ m ⦄ x = sequence-PlusN {n = n}⦃ m ⦄ 
                                                        (PlusN-f.map sequence-Ⓢ x)
      where module PlusN-f = Functor (Monad.is-functor (PlusN-is-monad {n}))

    PlusN-collect : ∀ {n}{a b} → n ⨁ (a + b) ≡ (n ⨁ a) ⨁ b
    PlusN-collect {n}{zero} = refl
    PlusN-collect {n}{suc a}{b} = PlusN-collect {Ⓢ n}{a}{b} 

  open Ⓢ-Type public
  open PlusN-Type public
  open Functors public
  open Monads public
  open Shapes public
  open StupidEquality public
