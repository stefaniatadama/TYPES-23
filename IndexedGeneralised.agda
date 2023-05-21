{-# OPTIONS --cubical --without-K --cubical-compatible --safe #-}

module IndexedGeneralised where

-- Proof that indexed containers are a special case of generalised containers

open import Containers renaming (Container to GenContainer)

open import Cubical.Foundations.Prelude renaming (J to path-ind ; _◁_ to _◁'_)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base 

private
  variable
    ℓ ℓ' ℓ'' : Level -- TODO: levels

open Category
    
-- Definition of indexed container

record IContainer (I : Type) (J : Type) : Type₁ where
  constructor _◁i_&_&_
  field
    S : J → Type
    P : (j : J) → S j → I → Type
    isSetS : (j : J) → isSet (S j)
    isSetP : (j : J) → (s : S j) → (i : I) → isSet (P j s i)  

open IContainer

record i-cat-obj (I : Type) (J : Type ) : Type₁ where
  constructor _&_&_
  field
    fam : I → Type
    fam-is-set : (i : I) → isSet (fam i)
    j : J

open i-cat-obj


module _ (I : Type) (J : Type) (isSetJ : isSet J) where

  i-cat-mor : i-cat-obj I J → i-cat-obj I J → Type
  i-cat-mor (A & _ & j) (B & _ & j') = Σ (j ≡ j') (λ _ → (k : I) → A k → B k)

  i-cat-id : {A : i-cat-obj I J} → i-cat-mor A A
  i-cat-id = refl , λ i a → a

  _⋆i_ : {A B C : i-cat-obj I J} → i-cat-mor A B → i-cat-mor B C  → i-cat-mor A C
  _⋆i_ (eq-ab , f-ab) (eq-bc , f-bc) = eq-ab ∙ eq-bc , λ i a → f-bc i (f-ab i a)

  i-cat-id-r : {A B : i-cat-obj I J} → (f : i-cat-mor A B) → _⋆i_ {A} {B} {B} f (i-cat-id {B}) ≡ f
  i-cat-id-r  (eq-f , f) = ΣPathP (sym (rUnit eq-f) , refl)

  i-cat-id-l : {A B : i-cat-obj I J} → (f : i-cat-mor A B) → _⋆i_ {A} {A} {B} (i-cat-id {A}) f ≡ f
  i-cat-id-l (eq-f , f) = ΣPathP (sym (lUnit eq-f) , refl)

  i-cat-assoc : {A B C D : i-cat-obj I J} → (f : i-cat-mor A B) (g : i-cat-mor B C) (h : i-cat-mor C D) →
                _⋆i_ {A} {C} {D} (_⋆i_ {A} {B} {C} f g) h ≡
                _⋆i_ {A} {B} {D} f (_⋆i_ {B} {C} {D} g h) 
  i-cat-assoc (eq-ab , ab) (eq-bc , bc) (eq-cd , cd) =
    ΣPathP (sym (assoc eq-ab eq-bc eq-cd) , funExt (λ i → funExt (λ a → refl)))

  i-cat-homs-sets : {A B : i-cat-obj I J} → isSet (i-cat-mor A B)
  i-cat-homs-sets {_ & _ & j} {B & setB & k} = isSetΣ (isProp→isSet (isSetJ j k)) λ eq → isSetΠ2 (λ i _ → setB i)

  i-cat : Category (ℓ-suc ℓ-zero) ℓ-zero
  i-cat = record
            { ob = i-cat-obj I J
            ; Hom[_,_] = i-cat-mor
            ; id = λ {A} → i-cat-id {A}
            ; _⋆_ = λ {A} {B} {C} → _⋆i_ {A} {B} {C}
            ; ⋆IdL = λ {A} {B} → i-cat-id-l {A} {B}
            ; ⋆IdR = λ {A} {B} → i-cat-id-r {A} {B}
            ; ⋆Assoc = λ {A} {B} {C} {D} → i-cat-assoc {A} {B} {C} {D}
            ; isSetHom = λ {A} {B} → i-cat-homs-sets {A} {B}
            }
               
  ⟦_⟧-i : IContainer I J → (I → Type ℓ'') → (J → Type ℓ'')
  ⟦_⟧-i (S ◁i P & _ & _) A j = Σ (S j) (λ s → (i : I) → P j s i → A i) 
  
  ⟦_⟧-g : GenContainer i-cat → (i-cat .ob → Type )
  ⟦_⟧-g (S ◁ P & _) X  = Σ S (λ s → i-cat [ P s , X ])

  isomorphism : (IC : IContainer I J) (A : I → Type) (setA : (i : I) → isSet (A i)) (j : J) →
                Iso (⟦ IC ⟧-i A j)
                    (⟦ Σ J (S IC) ◁ (λ { (k , sk) → (P IC) k sk & (isSetP IC) k sk & k}) & isSetΣ (isSetJ) (λ j → isSetS IC j) ⟧-g
                     (A & setA & j))
  isomorphism IC A setA j = iso to from sec' ret' 
    where
      to : ⟦ IC ⟧-i A j → Σ (Σ J (S IC)) (λ s → Σ (fst s ≡ j) (λ _ → (k : I) → P IC (fst s) (snd s) k → A k))
      to (si , pi) = (j , si) , (refl , pi)

      from : Σ (Σ J (S IC)) (λ s → Σ (fst s ≡ j) (λ _ → (k : I) → P IC (fst s) (snd s) k → A k)) → ⟦ IC ⟧-i A j
      from ((j' , sj') , (eq , f)) = subst (S IC) eq sj' ,
                                     λ i p → f i (transport (λ k → P IC (eq (~ k)) (subst-filler (S IC) eq sj' (~ k)) i) p)
                       
      sec' : (b : Σ (Σ J (S IC)) (λ s → Σ (fst s ≡ j) (λ _ → (k : I) → P IC (fst s) (snd s) k → A k))) →
             ((j , fst (from b)) , ((λ _ → j) , snd (from b))) ≡ b
      sec' ((k , sk) , eq , f) = ΣPathP ((ΣPathP (sym eq , symP (transport-filler (λ i → S IC (eq i)) sk))) ,
                                          ΣPathP ((λ i₁ i₂ → eq (~ i₁ ∨ i₂)) , λ k' k'' → aux k'' k'))
        where
          aux : (k' : I) → PathP (λ i → P IC (eq (~ i)) (transport-filler (λ i₁ → S IC (eq i₁)) sk (~ i)) k' → A k') (snd (from ((k , sk) , eq , f)) k') (f k')
          aux k' = toPathP
                     (funExt λ x → transportRefl _ ∙
                      cong (f k') (transportTransport⁻ (λ i₁ → P IC (eq (~ i₁))
                        (transport-filler (λ i₂ → S IC (eq i₂)) sk (~ i₁)) k') x)) 

      ret' : (a : ⟦ IC ⟧-i A j) → from (to a) ≡ a
      fst (ret' (s , f) i) = transportRefl s i
      snd (ret' (s , f) i) i' = mjo i
        where
          mjo : PathP (λ i → P IC j (transportRefl s i) i' → A i') (snd (from (to (s , f))) i') (f i')
          mjo = toPathP (funExt λ p → transportRefl _ ∙ cong (f i') (transportTransport⁻ (λ i₁ → P IC j (transport-filler (λ i₂ → S IC j) s (~ i₁)) i') p))
