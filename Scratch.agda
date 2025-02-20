module Scratch where
  open import OutsideIn.X
  open import OutsideIn.Instantiations.Simple as Simple
  import OutsideIn

  data DCs : OutsideIn.ℕ → Set where
    True : DCs 0
    False : DCs 0 

  data TCs : Set where
    BoolT : TCs


  open OutsideIn(Simple DCs)
 
  
  data ⊥ : Set where
  import OutsideIn.Inference.Separator as S
  open S(Simple DCs)

  ep : ∀ {v} → SConstraint v
  ep = SConstraint.ε
  _~_ : ∀ {v} → Simple.Type v → Simple.Type v → SConstraint v
  _~_ = SConstraint._∼_

  con : SConstraint  (TCs ⨁ 7) 
  con = (((((SConstraint.ε ∧′
                 (Var (suc (suc zero)) SConstraint.∼ Var (suc (suc (suc (suc zero))))))
               ∧′ (Var (suc (suc (suc zero))) SConstraint.∼ Var (suc (suc (suc (suc (suc zero)))))))
              ∧′ ((((Var (suc zero) SConstraint.∼ Var (suc (suc (suc zero)))) 
                    ∧′ (Var (suc zero) SConstraint.∼ Var (suc (suc (suc (suc (suc (suc (suc BoolT)))))))))
                   ∧′ (Var (suc (suc (suc (suc (suc (suc (suc BoolT))))))) SConstraint.∼ Var (suc (suc zero))))
                  ∧′ ((((Var zero SConstraint.∼ Var (suc (suc (suc zero)))) ∧′ (Var zero SConstraint.∼ Var (suc (suc (suc (suc (suc (suc (suc BoolT)))))))))
                      ∧′ (Var (suc (suc (suc (suc (suc (suc (suc BoolT))))))) SConstraint.∼ Var (suc (suc zero)))) ∧′ SConstraint.ε)))
             ∧′ (Var (suc (suc (suc (suc (suc (suc zero)))))) SConstraint.∼ ((funTy · Var (suc (suc (suc (suc zero))))) · Var (suc (suc (suc (suc (suc zero)))))))))

  con-s : SConstraint (SVar TCs 7)
  con-s = Functor.map sconstraint-is-functor svar-iso₁ con

  con′ : SConstraint (TCs ⨁ 1) 
  con′ = SConstraint.ε ∧′ ((Var zero) SConstraint.∼ (Var (suc BoolT)) )

  conn : SConstraint  (TCs ⨁ 2) 
  conn =  (Var (suc zero)) Simple.∼ (Var zero ⟶ Var zero)

  conn' : SConstraint  (TCs ⨁ 5)
  conn' = SConstraint.ε

  v = Simple.simplifier (record { eq = λ a b → true }) 1 ax SConstraint.ε conn
  w = Simple.simplifier (record { eq = λ a b → true }) 3 ax conn conn'


  open import Data.List


  

  -- 

  -- zero --> suc suc zero
  -- suc zero --> zero
  -- suc suc zero --> suc zero
  -- suc suc suc zero --> suc suc zero
  -- suc suc suc suc zero --> suc suc suc zero
  -- suc suc suc suc suc zero --> suc suc suc suc zero
  -- suc suc suc suc suc suc zero --> suc suc suc suc suc zero
  


  e : ∀ {tv} → Expression tv TCs _
  e = λ′ case Var (N zero) of 
                ( DC True  →′ Var (DC False)
                ∣ DC False →′ Var (DC True )
                ∣ esac
                )

  e2 : ∀ {tv ev} → Expression tv ev _
  e2 = λ′ Var (N zero)

  p2 : Program ⊥ TCs
  p2 = bind₂ 1 · e2 ∷ SConstraint.ε ⇒ Var zero ⟶ Var zero  
     , bind₁ e2
     , end  

  p : Program ⊥ TCs
  p = bind₂ 0 · e ∷ SConstraint.ε ⇒ Var BoolT ⟶ Var BoolT  
    , bind₁ e
    , end

  
  Γ : Environment ⊥ TCs
  Γ (DC True) = DC∀ 0 · [] ⟶ BoolT 
  Γ (DC False) = DC∀ 0 · [] ⟶ BoolT 
  Γ (N ()) 

  test = go ax Γ (record { eq = λ a b → true }) p
  test2 = go ax Γ (record { eq = λ a b → true }) p2
