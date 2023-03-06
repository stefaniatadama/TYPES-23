{-# OPTIONS --cubical #-}

-- PROOF THAT ⟦_⟧ IS FULL AND FAITHFUL FOR GENERALISED CONTAINERS

open import Cubical.Core.Everything

open import Cubical.Data.Prod
open import Cubical.Data.Nat
open import Cubical.Data.Fin
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude renaming (_◁_ to _◁'_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism 
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function renaming (_∘_ to _compos_)

-- Definition of category (with homsets which are h-sets)

record Category {m n : Level} : Type (ℓ-suc (ℓ-max m n)) where
  field
    -- Structure
    Obj : Type m 
    Hom : Obj → Obj → Type n 
    _∘_ : {A B C : Obj} → Hom B C → Hom A B → Hom A C
    id : {A : Obj} → Hom A A
    -- Properties
    assoc : {A B C D : Obj} (h : Hom C D) (g : Hom B C) (f : Hom A B) → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
    id-rneutr : {A B : Obj} (f : Hom A B) → f ∘ id ≡ f
    id-lneutr : {A B : Obj} (f : Hom A B) → id ∘ f ≡ f
    homs-are-sets : (A B : Obj) → isSet (Hom A B) 

open Category

-- Definition of generalised container parameterised by C

record Container (C : Category {ℓ-suc ℓ-zero} {ℓ-zero}) : Type₁ where
  constructor _◁_&_ 
  field
    S : Type
    P : S → Obj C
    isSetS : isSet S

open Container

-- Definition of the category of functors C → Set

record h-set : Type₁ where
  field
    set : Type
    is-set : isSet set

open h-set

isSet→ : (X Y : h-set) → isSet (set X → set Y)
isSet→ X Y = isSetΠ (λ x → is-set Y)

_●_ : ∀ {a b c} {A : Type a} {B : Type b} {C : Type c} → (B → C) → (A → B) → (A → C)
f ● g = λ x → f (g x)

SetC : Category {ℓ-suc ℓ-zero} {ℓ-zero}
SetC = record
         { Obj = h-set
         ; Hom = λ A B → set A → set B
         ; _∘_ = _●_ -- λ f g a → f (g a)
         ; id = λ a → a
         ; assoc = λ _ _ _ → refl
         ; id-rneutr = λ _ → refl
         ; id-lneutr = λ _ → refl
         ; homs-are-sets = isSet→
         }

record Functor {m m' n n'} (C : Category {m} {m'}) (D : Category {n} {n'}) : Type (ℓ-max m (ℓ-max m' (ℓ-max n n'))) where
  field
    -- Structure
    func-obj : Obj C → Obj D
    func-mor : {A B : Obj C} → (Hom C) A B → (Hom D) (func-obj A) (func-obj B)
    -- Properties
    func-id : {A : Obj C} → func-mor (id C {A}) ≡ (id D {func-obj A})
    func-comp : {U V W : Obj C} (g : (Hom C) V W) (f : (Hom C) U V) →
                func-mor ((_∘_) C g f) ≡ (_∘_) D (func-mor g) (func-mor f) 

open Functor

record NaturalTransformation {m m' n n'} {C : Category {m} {m'}} {D : Category {n} {n'}} (F G : Functor C D) : Type (ℓ-max m (ℓ-max m' (ℓ-max n n'))) where
  constructor _,nat:_
  field
    mors : (A : Obj C) → (Hom D) (func-obj F A) (func-obj G A)
    nat : (X Y : Obj C) (f : (Hom C) X Y) → (_∘_ D) (func-mor G f) (mors X) ≡ (_∘_ D) (mors Y) (func-mor F f)

open NaturalTransformation

∘-f : ∀ {m m'} {C : Category {m} {m'}} {F G H : Functor C SetC} →
      NaturalTransformation G H → NaturalTransformation F G → NaturalTransformation F H
mors (∘-f (β-m ,nat: β-n) (α-m ,nat: α-n)) A FA = β-m A (α-m A FA)
nat (∘-f (β-m ,nat: β-n) (α-m ,nat: α-n)) X Y xy =
  (λ i fx → β-n X Y xy i (α-m X fx)) ∙ (λ i fx → β-m Y (α-n X Y xy i fx))

id-mor-f : ∀ {m m'} {C : Category {m} {m'}} {F : Functor C SetC} →
           NaturalTransformation F F
id-mor-f {C = C} {F = F} = (λ A FA → FA) ,nat: λ X Y xy → id-rneutr SetC {func-obj F X} {func-obj F Y} (func-mor F xy) ∙ id-lneutr SetC {func-obj F X} {func-obj F Y} (func-mor F xy)

assoc-f : ∀ {m m'} {C : Category {m} {m'}} {F G H I : Functor C SetC}
          (γ : NaturalTransformation H I) (β : NaturalTransformation G H) (α : NaturalTransformation F G) →
          (∘-f  (∘-f γ β) α) ≡ (∘-f  γ (∘-f β α))
assoc-f {F = F} {I = I} (γ-m ,nat: γ-n) (β-m ,nat: β-n) (α-m ,nat: α-n) =
  cong₂ _,nat:_ refl (isProp→PathP (λ i → isPropΠ3 λ X Y f → isSet→ (func-obj F X) (func-obj I Y) _ _) _ _)          
id-rneutr-f : ∀ {m m'} {C : Category {m} {m'}} {F G : Functor C SetC}
              (α : NaturalTransformation F G) → ∘-f  α (id-mor-f) ≡ α
id-rneutr-f {F = F} {G = G} α = 
  cong₂ _,nat:_ refl (isProp→PathP (λ i → isPropΠ3 λ X Y f → isSet→ (func-obj F X) (func-obj G Y) _ _) _ _)

id-lneutr-f : ∀ {m m'} {C : Category {m} {m'}} {F G : Functor C SetC}
              (α : NaturalTransformation F G) → ∘-f (id-mor-f) α ≡ α
id-lneutr-f {F = F} {G = G} α =
  cong₂ _,nat:_ refl (isProp→PathP (λ i → isPropΠ3 λ X Y f → isSet→ (func-obj F X) (func-obj G Y) _ _) _ _)

isSetNatTrans : ∀ {m m'} {C : Category {m} {m'}} (F G : Functor C SetC) → isSet (NaturalTransformation F G)
mors (isSetNatTrans F G α β p q i j) X s =
  is-set (func-obj G X) (mors α X s) (mors β X s) (λ k → mors (p k) X s) (λ k → mors (q k) X s) i j
nat (isSetNatTrans F G α β p q i j) X Y xy k fx = cube i j k 
  where
    cube : Cube (λ j k → nat (p j) X Y xy k fx) (λ j k → nat (q j) X Y xy k fx)
                (λ i k → nat α X Y xy k fx) (λ i k → nat β X Y xy k fx)
                (λ i j → func-mor G xy (mors (isSetNatTrans F G α β p q i j) X fx))
                (λ i j → is-set (func-obj G Y) (mors α Y (func-mor F xy fx)) (mors β Y (func-mor F xy fx))
                       (λ k₁ → mors (p k₁) Y (func-mor F xy fx))
                       (λ k₁ → mors (q k₁) Y (func-mor F xy fx)) i j)
    cube = isSet→SquareP (λ i j → isOfHLevelPath 2 (is-set (func-obj G Y)) _ _) _ _ _ _

Func : ∀ {m m'} (C : Category {m} {m'}) → Category
Func C = record
           { Obj = Functor C SetC
           ; Hom = NaturalTransformation
           ; _∘_ = ∘-f
           ; id = id-mor-f
           ; assoc = assoc-f
           ; id-rneutr = id-rneutr-f
           ; id-lneutr = id-lneutr-f
           ; homs-are-sets = isSetNatTrans
           }

-- Defining machinery for Proof 2

record ProFunctor {m m'} (C : Category {m} {m'}) : Type (ℓ-suc (ℓ-max m m')) where
  field
    -- Structure
    profunc-obj : Obj C → Obj C → Obj SetC
    profunc-mor : {P P' Q Q' : Obj C} → (Hom C) P P' → (Hom C) Q Q' →
                  (Hom SetC) (profunc-obj P' Q) (profunc-obj P Q')
    -- Properties
    profunc-id : {P Q : Obj C} → profunc-mor (id C {P}) (id C {Q}) ≡ (id SetC {profunc-obj P Q})
    profunc-comp : {P Q R S T U : Obj C} (g : (Hom C) Q R) (g' : (Hom C) P Q) (f : (Hom C) T U) (f' : (Hom C) S T)
                   → profunc-mor ((_∘_ C) g g') ((_∘_ C) f f') ≡
                   (_∘_ SetC) {profunc-obj R S} {profunc-obj Q T} {profunc-obj P U}
                   (profunc-mor g' f) (profunc-mor g f')
{-
profunc-comp: 
P -g'-> Q -g-> R
S -f'-> T -f-> U
P (g' ∘ g , f' ∘ f) ≡ P (g , f') ∘ P (g' , f)
-}

open ProFunctor

-- nats F G X- X+ = F X- → G X+

nats : ∀ {m m'} → (C : Category {m} {m'}) (F G : Functor C SetC) → ProFunctor C
nats C F G = record
               { profunc-obj = λ c c' →
                                 record { set = (Hom SetC) (func-obj F c) (func-obj G c') ;
                                          is-set = isSetΠ (λ _ → is-set (func-obj G c')) }
               ; profunc-mor = λ f g h x → func-mor G g (h (func-mor F f x))
               ; profunc-id = funExt λ f → funExt λ fx →
                              cong (λ X → func-mor G (id C) (f X)) (funExt⁻ (func-id F) fx) ∙
                              funExt⁻ (func-id G) (f fx) 
               ; profunc-comp = λ {P} {Q} {R} {S} {T} {U} qr pq tu st →
                              funExt λ rs → funExt λ Fp →
                              cong (λ X → func-mor G ((_∘_ C) tu st) (rs X)) (funExt⁻ (func-comp F qr pq) Fp) ∙
                              funExt⁻ (func-comp G tu st) (rs (func-mor F qr (func-mor F pq Fp)))
               }

record ∫ {m m'} {C : Category {m} {m'}} (F : ProFunctor C) : Type (ℓ-suc (ℓ-max m m')) where
  constructor end
  field
    funcs : (c : Obj C) → set (profunc-obj F c c)
    nat : (c d : Obj C) (f : (Hom C) c d) →
          profunc-mor F ((id C) {c}) f (funcs c) ≡ profunc-mor F f ((id C) {d}) (funcs d)

{-
nat is the commutative diamond for wedges
           Obj C
         /        \    
funcs c /          \ funcs d
       /            \
      /              \
F c c                 F d d
     \               /
      \             /
F id f \           / F f id
        \         /
           F c d   
-}

open ∫

-- (X : Functor C SetC) is representable if (X ≅ H^ A) for some (A : Obj C)

H^ : ∀ {m} {C : Category {m} {ℓ-zero}} (A : Obj C) → Functor C SetC
H^ {C = C} A = record
             { func-obj = λ B → record { set = (Hom C) A B ; is-set = (homs-are-sets) C A B } ;
               func-mor = _∘_ C ;
               func-id = funExt (id-lneutr C) ;
               func-comp = λ g f → funExt (assoc C g f) }


module _ {C : Category {ℓ-suc ℓ-zero} {ℓ-zero}} where

    -- Category Cont with objects Container C

    record _⇒_ (C₁ C₂ : Container C) : Type where
      constructor _◁_
      field
        u : S C₁ → S C₂
        f : (s : S C₁) → Hom C (P C₂ (u s)) (P C₁ s) 

    open _⇒_

    _∘c_ : {C₁ C₂ C₃ : Container C} → C₂ ⇒ C₃ → C₁ ⇒ C₂ → C₁ ⇒ C₃
    _∘c_ (v ◁ g) (u ◁ f) = (λ a → v (u a)) ◁ λ a → (_∘_ C) (f a) (g (u a))

    id-c : {Con : Container C} → Con ⇒ Con
    id-c = (λ s → s) ◁ λ _ → id C

    assoc-c : {C₁ C₂ C₃ C₄ : Container C} (h : C₃ ⇒ C₄) (g : C₂ ⇒ C₃) (f : C₁ ⇒ C₂) →
               (h ∘c g) ∘c f ≡ h ∘c (g ∘c f)
    assoc-c (w ◁ h) (v ◁ g) (u ◁ f) i = (λ a → w (v (u a))) ◁ λ a → assoc C (f a) (g (u a)) (h (v (u a))) (~ i)

    isSet⇒ : (C₁ C₂ : Container C) → isSet (C₁ ⇒ C₂)
    u (isSet⇒ (A ◁ B & set-A) (E ◁ F & set-C) m n p q i j) a =
      set-C (u m a) (u n a) (λ k → u (p k) a) (λ k → u (q k) a) i j
    f (isSet⇒ (A ◁ B & set-A) (E ◁ F & set-C) m n p q i j) a = isSet→SquareP
        {A = λ i j → Hom C (F (set-C (u m a) (u n a) (λ k → u (p k) a) (λ k → u (q k) a) i j)) (B a)}
        (λ i j → homs-are-sets C (F (set-C (u m a) (u n a) (λ k → u (p k) a) (λ k → u (q k) a) i j)) (B a))
        (λ k → f (p k) a)
        (λ k → f (q k) a)
        (λ _ → f m a)
        (λ _ → f n a)
        i j

    Cont : Category {ℓ-suc ℓ-zero} {ℓ-zero}
    Cont = record
             { Obj = Container C
             ; Hom = _⇒_
             ; _∘_ = _∘c_
             ; id = id-c
             ; assoc = assoc-c
             ; id-rneutr = λ m i → u m ◁ λ a → id-lneutr C (f m a) i 
             ; id-lneutr = λ m i → u m ◁ λ a → id-rneutr C (f m a) i
             ; homs-are-sets = isSet⇒ 
             }

   -- Defining functor ⟦_⟧ : Cont → Func

    record cont-func (A : Type) (B : A → Obj C) (X : Obj C) : Type where
      constructor _<_
      field
        shape : A
        pos : (Hom C) (B shape) X

    open cont-func

    isSetContFunc : (A : Type) (B : A → Obj C) (X : Obj C) (isSetA : isSet A) → isSet (cont-func A B X)
    shape (isSetContFunc A B X setA s₁ s₂ p q i j) =
      setA (shape s₁) (shape s₂) (λ k → shape (p k)) (λ k → shape (q k)) i j
    pos (isSetContFunc A B X setA s₁ s₂ p q i j) = 
      isSet→SquareP
        {A = λ i j → (Hom C) (B (setA (shape s₁) (shape s₂) (λ k → shape (p k)) (λ k → shape (q k)) i j)) X}
        (λ i j → (homs-are-sets C) (B (setA (shape s₁) (shape s₂) (λ k → shape (p k)) (λ k → shape (q k)) i j)) X)
        (λ k → pos (p k))
        (λ k → pos (q k))
        (λ _ → pos s₁)
        (λ _ → pos s₂)
        i j
        
    cont-mor : {A : Type} {B : A → Obj C} {X Y : Obj C} (f : (Hom C) X Y) → cont-func A B X → cont-func A B Y
    cont-mor f (s < g) = s < (_∘_ C) f g 

    ⟦_⟧-obj : Container C → Functor C SetC
    ⟦ (A ◁ B & set-A) ⟧-obj = record
                              { func-obj = λ X → record { set = cont-func A B X ;
                                                         is-set = isSetContFunc A B X set-A
                                                        } ;
                               func-mor = λ {X} {Y} f → cont-mor {A} {B} {X} {Y} f; 
                               func-id = funExt λ {(a < b) i → a < id-lneutr C b i } ;
                               func-comp = λ g f i (a < b) → a < (assoc C) g f b i
                              }

    ⟦_⟧-mor : {C₁ C₂ : Container C} → C₁ ⇒ C₂ → NaturalTransformation ⟦ C₁ ⟧-obj ⟦ C₂ ⟧-obj
    mors (⟦_⟧-mor (u ◁ f)) X (s < p) = u s < (_∘_ C) p (f s)
    nat (⟦_⟧-mor (u ◁ f)) X Y xy i (a < b) = u a < (assoc C) xy b (f a) (~ i)

    ⟦_⟧-id : {C₁ : Container C} → ⟦_⟧-mor {C₁} {C₁} (id-c {C₁}) ≡ id-mor-f
    mors (⟦_⟧-id {S ◁ P & set-S} i) X (s < p) = s < id-rneutr C p i
    nat (⟦_⟧-id {S ◁ P & set-S} i) X Y xy j (s < p) = square i j
      where
        square : Square
                  (λ j → nat (⟦_⟧-mor {S ◁ P & set-S} {S ◁ P & set-S} id-c) X Y xy j (s < p))
                  (λ j → nat (id-mor-f {F = ⟦ S ◁ P & set-S ⟧-obj }) X Y xy j (s < p))
                  (λ i → (cont-mor xy ● mors (⟦_⟧-id {S ◁ P & set-S} i) X) (s < p))
                  (λ i → (mors (⟦_⟧-id {S ◁ P & set-S} i) Y ● cont-mor xy) (s < p))
        square = isSet→SquareP
                  (λ i j → isSetContFunc S P Y set-S)
                  (λ j → nat (⟦_⟧-mor {S ◁ P & set-S} {S ◁ P & set-S} id-c) X Y xy j (s < p))
                  (λ j → nat (id-mor-f {F = ⟦ S ◁ P & set-S ⟧-obj }) X Y xy j (s < p))
                  (λ i → s < (C ∘ xy) (id-rneutr C p i))
                  (λ i → s < id-rneutr C ((C ∘ xy) p) i) 

    ⟦_⟧-comp : {U V W : Container C} (g : V ⇒ W) (h : U ⇒ V) → ⟦ g ∘c h ⟧-mor ≡ ∘-f ⟦ g ⟧-mor ⟦ h ⟧-mor
    mors (⟦_⟧-comp {U} {V} {W} (ug ◁ fg) (uh ◁ fh) i) A (s < p) = ug (uh s) < (assoc C) p (fh s) (fg (uh s)) (~ i)
    nat (⟦_⟧-comp {U} {V} {W} (ug ◁ fg) (uh ◁ fh) i) X Y xy j (s < p) = square i j
      where
        square : Square
                 (λ j → nat (⟦_⟧-mor {U} {W} (_∘c_ {U} {V} {W} (ug ◁ fg) (uh ◁ fh))) X Y xy j (s < p))
                 (λ j → nat (∘-f (⟦_⟧-mor {V} {W} (ug ◁ fg)) (⟦_⟧-mor {U} {V} (uh ◁ fh))) X Y xy j (s < p))
                 (λ i → ug (uh s) < (C ∘ xy) (assoc C p (fh s) (fg (uh s)) (~ i)))
                 (λ i → ug (uh s) < assoc C ((C ∘ xy) p) (fh s) (fg (uh s)) (~ i))
        square = isSet→SquareP (λ i j → isSetContFunc (S W) (P W) Y (isSetS W)) _ _ _ _

    ⟦_⟧ : Functor Cont (Func C)
    ⟦_⟧ = record
          { func-obj = ⟦_⟧-obj ;
            func-mor = ⟦_⟧-mor ;
            func-id = λ {A} → ⟦_⟧-id {A} ;
            func-comp = ⟦_⟧-comp
          }
          
    ------

    _-fully-faithful : {m m' n n' : Level} {C : Category {m} {n}} {D : Category {m'} {n'}} →
                       Functor C D → Type (ℓ-max (ℓ-max m n) n')
    _-fully-faithful {C = C} {D = D} F =
      (X Y : Obj C) → Iso ((Hom C) X Y) ((Hom D) ((func-obj F) X) ((func-obj F) Y))

    -- Proof 1 that the functor ⟦_⟧ is full and faithful
    -- Adapted from 'Containers: Constructing strictly positive types'

    fun : (X Y : Container C) → X ⇒ Y → NaturalTransformation ⟦ X ⟧-obj ⟦ Y ⟧-obj
    fun X Y = ⟦_⟧-mor {X} {Y}

    inv : (X Y : Container C) → NaturalTransformation ⟦ X ⟧-obj ⟦ Y ⟧-obj → X ⇒ Y
    inv (S ◁ P & set-S) (T ◁ Q & set-T) (mors ,nat: nat) = (λ s → shape (tq s)) ◁ (λ s → pos (tq s))
      where
        tq : (s : S) → cont-func T Q (P s)
        tq s = mors (P s) (s < id C {P s})

    sec : (X Y : Container C) → ∀ α → (fun X Y) ((inv X Y) α) ≡ α
    sec (S ◁ P & set-S) (T ◁ Q & set-T) (mors ,nat: nat) =
      cong₂
        _,nat:_
        (funExt
          (λ X → funExt
            λ {(s < h) → funExt⁻ (nat (P s) X h) (s < id C) ∙ cong (λ Z → mors X (s < Z)) (id-rneutr C h)}))
       ((isProp→PathP (λ i → isPropΠ3 (λ X Y f → isSetΠ (λ _ → isSetContFunc T Q Y set-T) _ _)) _ _))

    ret : (X Y : Container C) → ∀ mor → (inv X Y) ((fun X Y) mor) ≡ mor
    ret C₁ C₂ (u ◁ f) i = u ◁ λ s → id-lneutr C (f s) i

    ⟦_⟧-fully-faithful : ⟦_⟧ -fully-faithful
    ⟦_⟧-fully-faithful X Y = iso (fun X Y) (inv X Y) (sec X Y) (ret X Y)

    
    -- Proof 2 that the functor ⟦_⟧ is full and faithful
    -- Uses the Yoneda lemma

    yoneda-lemma : (F : Functor C SetC) (A : Obj C) → Iso (∫ (nats C (H^ A) F)) (set (func-obj F A))
    yoneda-lemma F A = iso (yoneda-to F A) (yoneda-from F A) (λ fa → funExt⁻ (func-id F) fa) (yoneda-ret F A)
      where
        yoneda-to : (F : Functor C SetC) (A : Obj C) →  ∫ (nats C (H^ A) F) → set (func-obj F A)
        yoneda-to F A record { funcs = funcs ; nat = nat } = funcs A (id C)

        yoneda-from : (F : Functor C SetC) (A : Obj C) → set (func-obj F A) → ∫ (nats C (H^ A) F)
        funcs (yoneda-from F A p) Y g =  (func-mor F g) p
        nat (yoneda-from F A p) X Y g = funExt λ homAX i →
          funExt⁻ (func-id F) (funExt⁻ (func-comp F g (id-lneutr C  homAX i)) p (~ i)) (~ i) 

        yoneda-ret : (F : Functor C SetC) (A : Obj C) → retract (yoneda-to F A) (yoneda-from F A)
        funcs (yoneda-ret F A α i) X ax =
          (((sym (cong (λ Z → func-mor F ax (funcs α A Z)) (id-rneutr C (id C))) ∙
          (funExt⁻ (nat α A X ax) (id C))) ∙
          (funExt⁻ (func-id F) (funcs α X ((C ∘ ax) (id C))))) ∙
          cong (λ Z → funcs α X Z) (id-rneutr C ax))
          i   
        nat (yoneda-ret F A α i) X Y xy j ax = square i j
          where
            square : Square
                      (λ j → nat (yoneda-from F A (yoneda-to F A α)) X Y xy j ax)
                      (λ j → nat α X Y xy j ax)
                      (λ i → func-mor F xy
                         (((((λ j →
                               func-mor F ((C ∘ id C) ax) (funcs α A (id-rneutr C (id C) (~ j))))
                            ∙ funExt⁻ (nat α A X ((C ∘ id C) ax)) (id C))
                           ∙ funExt⁻ (func-id F) (funcs α X ((C ∘ (C ∘ id C) ax) (id C))))
                          ∙ (λ j → funcs α X (id-rneutr C ((C ∘ id C) ax) j)))
                         i))
                      (λ i → func-mor F (id C)
                         (((((λ j →
                                func-mor F ((C ∘ xy) ax) (funcs α A (id-rneutr C (id C) (~ j))))
                             ∙ funExt⁻ (nat α A Y ((C ∘ xy) ax)) (id C))
                            ∙ funExt⁻ (func-id F) (funcs α Y ((C ∘ (C ∘ xy) ax) (id C))))
                           ∙ (λ j → funcs α Y (id-rneutr C ((C ∘ xy) ax) j)))
                          i))
            square = isSet→SquareP (λ _ _ → is-set (func-obj F Y)) _ _ _ _

    tt-aoc : {A : Type}{B : A → Type}{C : (a : A) → B a → Type} → Iso ((a : A) → Σ (B a) (λ b → C a b))
             (Σ ((a : A) → B a) (λ f → (a : A) → C a (f a)))
    tt-aoc = iso
             (λ f → (λ a → fst (f a)) , λ a → snd (f a)) (λ {(f , g) → λ a → f a , g a})
             (λ _ → refl)
             (λ _ → refl)

    depCodomainIso : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : A → Type ℓ'} {C : A → Type ℓ''}
               → ((a : A) → Iso (B a) (C a))
               → Iso ((a : A) → B a) ((a : A) → C a)
    Iso.fun (depCodomainIso is) g a = Iso.fun (is a) (g a) 
    Iso.inv (depCodomainIso is) g a = Iso.inv (is a) (g a)
    Iso.rightInv (depCodomainIso is) g = funExt (λ a → Iso.rightInv (is a) (g a))
    Iso.leftInv (depCodomainIso is) g = funExt (λ a → Iso.leftInv (is a) (g a))
    
    ⇒≅end : (C₁ C₂ : Container C) → Iso (C₁ ⇒ C₂) (∫ (nats C ⟦ C₁ ⟧-obj ⟦ C₂ ⟧-obj))
    ⇒≅end (S ◁ P & set-S) (T ◁ Q & set-T) =
      (S ◁ P & set-S) ⇒ (T ◁ Q & set-T)
      Iso⟨ iso (λ {(u ◁ f) → u , f}) (λ {(u , f) → u ◁ f}) (λ _ → refl) (λ _ → refl) ⟩
      Σ (S → T) (λ f → (s : S) → (Hom C) (Q (f s)) (P s))
      Iso⟨ invIso tt-aoc ⟩
      ((s : S) → Σ T (λ t → (Hom C) (Q t) (P s)))
      Iso⟨ iso (λ f s → fst (f s) < snd (f s)) (λ f s → shape (f s) , pos (f s)) (λ _ → refl) (λ _ → refl) ⟩
      ((s : S) → set (func-obj ⟦ (T ◁ Q & set-T) ⟧-obj (P s)))
      Iso⟨ depCodomainIso (λ s → invIso (yoneda-lemma ⟦ (T ◁ Q & set-T) ⟧-obj (P s))) ⟩
      ((s : S) → ∫ (nats C (H^ (P s)) ⟦ (T ◁ Q & set-T) ⟧-obj) )
      Iso⟨ iso (λ f → record { funcs = λ X → λ {(s < h) → funcs (f s) X h } ;
                               nat = λ X Y homXY → funExt (λ {(s < h) → funExt⁻ (nat (f s) X Y homXY) h})})
               (λ α s → record { funcs = λ X homPsX → funcs α X (s < homPsX) ;
                                 nat = λ X Y homXY → funExt (λ homPsX → funExt⁻ (nat α X Y homXY) (s < homPsX)) })
               (λ _ → refl)
               (λ _ → refl) ⟩
      ∫ (nats C ⟦ (S ◁ P & set-S) ⟧-obj ⟦ (T ◁ Q & set-T) ⟧-obj)
      ∎Iso

    end≅nats : (C₁ C₂ : Container C) → Iso (∫ (nats C ⟦ C₁ ⟧-obj ⟦ C₂ ⟧-obj)) (NaturalTransformation ⟦ C₁ ⟧-obj ⟦ C₂ ⟧-obj)
    end≅nats (S ◁ P & set-S) (T ◁ Q & set-T) = iso to from to-from from-to
      where
        from : NaturalTransformation ⟦ (S ◁ P & set-S) ⟧-obj ⟦ (T ◁ Q & set-T) ⟧-obj →
               ∫ (nats C ⟦ (S ◁ P & set-S) ⟧-obj ⟦ (T ◁ Q & set-T) ⟧-obj)
        from (mors ,nat: nat) = record
                              { funcs = mors ;
                                nat = λ X Y homXY i →
                                      λ spx → shape (nat X Y homXY i (shape spx < id-lneutr C (pos spx) i))
                                              <
                                              id-lneutr C
                                                (pos (nat X Y homXY i (shape spx < id-lneutr C (pos spx) i))) (~ i)
                               }
                               
        to : ∫ (nats C ⟦ (S ◁ P & set-S)  ⟧-obj ⟦ (T ◁ Q & set-T) ⟧-obj) →
             NaturalTransformation ⟦ (S ◁ P & set-S) ⟧-obj ⟦ (T ◁ Q & set-T) ⟧-obj
        mors (to record { funcs = funcs ; nat = nat }) = funcs
        nat (to record { funcs = funcs ; nat = nat }) A B g = funExt pf
          where
            lem : (S : Type) (P : S → Obj C) (X : Obj C) → (x : (cont-func S P X)) →
                  x ≡ (shape x < (C ∘ id C) (pos x))
            lem S P X x i = shape x < id-lneutr C (pos x) (~ i)

            pf : (x : (cont-func S P A)) →
                 shape (funcs A x) < (C ∘ g) (pos (funcs A x)) ≡ funcs B (shape x < (C ∘ g) (pos x))
            pf x = cong (λ p → shape (funcs A p) < (C ∘ g) (pos (funcs A p))) (lem S P A x) ∙
                   funExt⁻ (nat A B g) x ∙
                   sym (lem T Q B (funcs B (shape x < (C ∘ g) (pos x))))

        to-from : (n : NaturalTransformation ⟦ (S ◁ P & set-S) ⟧-obj ⟦ (T ◁ Q & set-T) ⟧-obj) → to (from n) ≡ n   
        mors (to-from (mors ,nat: nat) i) = mors
        nat (to-from (mors ,nat: nat) i) X Y xy j x = square i j
          where
            square : Square
                      (λ j → NaturalTransformation.nat (to (from (mors ,nat: nat))) X Y xy j x)
                      (λ j → nat X Y xy j x)
                      (λ i → shape (mors X x) < (C ∘ xy) (pos (mors X x))) --(cont-mor xy ● mors X) x)
                      (λ i → mors Y (shape x < (C ∘ xy) (pos x))) --(mors Y ● cont-mor xy) x)
            square = isSet→SquareP (λ i j → isSetContFunc T Q Y set-T) _ _ _ _

        from-to : (α : ∫ (nats C ⟦ S ◁ P & set-S ⟧-obj ⟦ T ◁ Q & set-T ⟧-obj)) → from (to α) ≡ α
        funcs (from-to (end f n) i) = f
        nat (from-to (end f n) i) X Y xy j x = square i j
          where
            square : Square
                      (λ j → nat (from (to (end f n))) X Y xy j x)
                      (λ j → n X Y xy j x)
                      (λ i → cont-mor xy (f X (cont-mor (id C) x)))
                      (λ i → cont-mor (id C) (f Y (cont-mor xy x)))
            square = isSet→SquareP (λ i j → isSetContFunc T Q Y set-T) _ _ _ _         

    ⟦_⟧-fully-faithful' : ⟦_⟧ -fully-faithful
    ⟦_⟧-fully-faithful' X Y = compIso (⇒≅end X Y) (end≅nats X Y)

-- Example

ListC : Container SetC
ListC = ℕ ◁ (λ n → record { set = Fin n ; is-set = isSetFin }) & isSetℕ

ListF : Functor SetC SetC
ListF = ⟦ ListC ⟧-obj

