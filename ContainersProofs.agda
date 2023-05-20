{-# OPTIONS --cubical --without-K --cubical-compatible --safe #-}

module ContainersProofs where

-- PROOF THAT ⟦_⟧ IS FULL AND FAITHFUL FOR GENERALISED CONTAINERS

open import Containers

open import Agda.Builtin.Cubical.HCompU

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude hiding (_◁_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism 
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Fin

open import Cubical.Categories.Category.Base 
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation hiding (_⟦_⟧)
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Yoneda

private
  variable
    ℓ ℓ' ℓ'' ℓ''' ℓ'''' : Level

open Category
open Functor
open NatTrans

module ContsProofs {C : Category ℓ ℓ'} where

    open Containers.Conts {ℓ} {ℓ'} {C}   

    -- Proof 1 that the functor ⟦_⟧ is full and faithful
    -- Adapted from 'Containers: Constructing strictly positive types'

    ⟦_⟧-fully-faithful : isFullyFaithful ⟦_⟧
    equiv-proof (⟦_⟧-fully-faithful (S ◁ P & set-S) (T ◁ Q & set-T)) (natTrans mors nat) =
      (fib (natTrans mors nat) , fib-pf) , unique
      where
        fib : NatTrans ⟦ (S ◁ P & set-S) ⟧-obj ⟦ (T ◁ Q & set-T) ⟧-obj → (S ◁ P & set-S) ⇒c (T ◁ Q & set-T)
        fib (natTrans mors nat) = (λ s → fst (tq s)) ◁ (λ s → snd (tq s))
          where
            tq : (s : S) → cont-func T Q (P s)
            tq s = mors (P s) (s , C .id {P s}) 

        fib-pf : ⟦ fib (natTrans mors nat) ⟧-mor ≡ (natTrans mors nat)
        fib-pf = cong₂
                   natTrans
                   ((funExt
                       λ X → funExt λ {(s , h) → sym (funExt⁻ (nat h) (s , C .id)) ∙ cong (λ Z → mors X (s , Z)) (C .⋆IdL h)})) 
                   (isProp→PathP (λ i → isPropImplicitΠ2 (λ X Y → isPropΠ (λ f →
                     isSetΠ (λ _ → isSetContFunc T Q Y set-T) _ _))) _ _) 

        ret : ∀ X→Y → fib (⟦ X→Y ⟧-mor) ≡ X→Y
        ret (u ◁ f) i = u ◁ λ s → C .⋆IdR (f s) i
        
        unique : (y : Helpers.fiber (⟦_⟧-mor) (natTrans mors nat)) → (fib (natTrans mors nat), fib-pf ) ≡ y
        unique (m , m-eq) = ΣPathP (cong (fib) (sym m-eq) ∙ ret m , square)
          where
            square : Square (λ i → fib-pf i)
                            (λ i → m-eq i)
                            (λ i → F-hom ⟦_⟧ (((λ i₁ → fib (m-eq (~ i₁))) ∙ ret m) i))
                            refl
            square = isSet→SquareP (λ _ _ → isSetNatTrans) _ _ _ _

    -- Proof 2 that the functor ⟦_⟧ is full and faithful
    -- Uses the Yoneda lemma

    tt-aoc : {A : Type ℓ''}{B : A → Type ℓ'''}{C : (a : A) → B a → Type ℓ''''} → Iso ((a : A) → Σ (B a) (λ b → C a b))
             (Σ ((a : A) → B a) (λ f → (a : A) → C a (f a)))
    tt-aoc = iso
             (λ f → (λ a → fst (f a)) , λ a → snd (f a)) (λ {(f , g) → λ a → f a , g a})
             (λ _ → refl)
             (λ _ → refl)

    ⟦_⟧-fully-faithful' : isFullyFaithful ⟦_⟧
    equiv-proof (⟦_⟧-fully-faithful' (S ◁ P & isSetS) (T ◁ Q & isSetT)) (natTrans mors nat) =
      (cont-xy , cont-xy-eq) , unique
      where
        nat-trans : (s : S) → FUNCTOR C (SET ℓ') [ C [ P s ,-] , ⟦ T ◁ Q & isSetT ⟧-obj ]
        nat-trans s = natTrans (λ X → curry (mors X) s) nat'
          where
            nat' : N-hom-Type (C [ P s ,-]) ⟦ T ◁ Q & isSetT ⟧-obj (λ X → curry (mors X) s)
            nat' {X} {Y} X→Y = funExt (λ Ps→X → funExt⁻ (nat {X} {Y} X→Y) (s , Ps→X))

        apply-yo : (s : S) → cont-func T Q (P s)
        apply-yo s = (yoneda ⟦ T ◁ Q & isSetT ⟧-obj (P s)) .Iso.fun (nat-trans s)

        result : Σ (S → T) (λ f → (s : S) → C [ Q (f s) , P s ])
        result = tt-aoc .Iso.fun (apply-yo)

        cont-xy : Cont [ S ◁ P & isSetS , T ◁ Q & isSetT ]
        cont-xy = fst result ◁ snd result        

        cont-xy-eq : ⟦ cont-xy ⟧-mor ≡ natTrans mors nat 
        cont-xy-eq = cong₂
                       natTrans
                       (funExt
                         (λ X → funExt
                           (λ {(s , f) → sym (funExt⁻ (nat {P s} {X} f) (s , C .id)) ∙ cong (λ Z → mors X (s , Z)) (C .⋆IdL f)})))
                       ((isProp→PathP (λ i → isPropImplicitΠ2 (λ X Y → isPropΠ (λ f →
                         isSetΠ (λ _ → isSetContFunc T Q Y isSetT) _ _))) _ _))

        -- Compose heterogenous with homogenous equality
        comp-het-hom : {A : I → Type ℓ'} (x : A i0) (y : A i1) (z : A i1) → PathP (λ i → A i) x y → y ≡ z → PathP (λ i → A i) x z
        comp-het-hom {A} x y z p eq i = subst (λ c → PathP A x c) eq p i 
        
        unique : (y : Helpers.fiber (⟦_⟧-mor) (natTrans mors nat)) → (cont-xy , cont-xy-eq) ≡ y
        unique ((u ◁ f) , m-eq) =
          ΣPathP
            (cong₂ _◁_ (funExt (λ s i → fst (N-ob (m-eq (~ i)) (P s) (s , C .id))))
                       (funExt (λ s i → comp-het-hom
                                         (snd (mors (P s) (s , C .id)))
                                         (f s ⋆⟨ C ⟩ (C .id))
                                         (f s)
                                         (λ j → snd (N-ob (m-eq (~ j)) (P s) (s , C .id)))
                                         (C .⋆IdR (f s)) i)) , 
            square) 
             where
               square : Square (λ i → cont-xy-eq i)
                               (λ i → m-eq i)
                               (λ i → ⟦_⟧-mor {S ◁ P & isSetS} {T ◁ Q & isSetT}
                                              (funExt (λ s i₁ → fst (N-ob (m-eq (~ i₁)) (P s) (s , C .id))) i ◁
                                              funExt (λ s i₁ → comp-het-hom
                                                                 (snd (mors (P s) (s , C .id)))
                                                                 (seq' C (f s) (C .id)) (f s)
                                                                 (λ i₂ → snd (N-ob (m-eq (~ i₂)) (P s) (s , C .id)))
                                                                 (C .⋆IdR (f s)) i₁) i))
                               (λ j → natTrans mors nat)
               square = isSet→SquareP (λ _ _ → isSetNatTrans) _ _ _ _        
    
-- Example

open Containers.Conts {C = SET (ℓ-zero)}

ListC : Container (SET (ℓ-zero))
ListC = ℕ ◁ (λ n → Fin n , isSetFin) & isSetℕ


ListF : Functor (SET (ℓ-zero)) (SET (ℓ-zero))
ListF = ⟦ ListC ⟧-obj
