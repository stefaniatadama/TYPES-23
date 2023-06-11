{-# OPTIONS --without-K --guardedness --cubical --allow-unsolved-metas #-}

module InductiveContainers where

-- Work in progress

-- Formalisation of Prop. 5.3 and Prop. 5.4 from
-- 'Containers: Constructing strictly positive types'

open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Nat
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism

private
  variable
    a ℓ : Level
    A B C : Set a

data W (S : Set) (P : S → Set) : Set where
  sup-W : (s : S) → (P s → W S P) → W S P

W-rec : (S : Set) (P : S → Set) (M : W S P → Set) →
        (e : {s : S} {f : P s → W S P} → ((p : P s) → M (f p)) → M (sup-W s f)) →
        (w : W S P) → M w
W-rec S P M e (sup-W s f) = e {s} {f} (λ p → W-rec S P M e (f p))

record M (S : Set) (P : S → Set) : Set where
  constructor sup-M
  coinductive
  field
    shape : S
    pos : P shape → M S P

open M

M-coiter : (S : Set) (P : S → Set) (N : Set) →
           (s : N → S) →
           ((n : N) → P (s n) → N) →
           N → M S P
shape (M-coiter S P N s p n) = s n         
pos (M-coiter S P N s p n) posi = M-coiter S P N s p (p n posi)

record Spec : Set₁ where
  field
    Ind : Set
    S : Set
    P : Ind → S → Set
    Q : S → Set
    X : Ind → Set
    Y : Set
    α : Σ S (λ s → Σ ((i : Ind) → P i s → X i) (λ _ → Q s → Y)) → Y
    βs : Y → S
    βg : (y : Y) → (i : Ind) → P i (βs y) → X i
    βh : (y : Y) → Q (βs y) → Y

module _ (spec : Spec) where

  open Spec spec
  open M
  
  record ContFuncAlg (S : Set) (P : S → Set) : Set₁ where
    constructor alg
    field
      Z : Set
      χ : (s : S) → (P s → Z) → Z

  open ContFuncAlg

  WAlg : ContFuncAlg S Q
  WAlg = alg (W S Q) sup-W

  MAlg : ContFuncAlg S Q
  MAlg = alg (M S Q) sup-M

  -- we have (propositional) η equality for M in Cubical Agda
  M-eta-eq : (m : M S Q) → sup-M (shape m) (pos m) ≡ m
  shape (M-eta-eq m i) = shape m
  pos (M-eta-eq m i) = pos m
  
  data Pos (FP : ContFuncAlg S Q) (i : Ind) : Z FP → Set where
    here : {s : S} {f : Q s → Z FP} → P i s → Pos FP i ((χ FP) s f)
    below : {s : S} {f : Q s → Z FP} → (q : Q s) → Pos FP i (f q) → Pos FP i ((χ FP) s f)

  Pos-rec : (FP : ContFuncAlg S Q) (i : Ind) →
            (M : Z FP → Set) →
            (h : {s : S} {f : Q s → Z FP} → P i s →
                  M ((χ FP) s f)) →
            (b : {s : S} {f : Q s → Z FP} (q : Q s) → M (f q) →
                  M ((χ FP) s f)) →
            (z : Z FP) → Pos FP i z → M z
  Pos-rec FP i M h b .((χ FP) s f) (here {s} {f} p) = h p
  Pos-rec FP i M h b .((χ FP) s f) (below {s} {f} q pos) = b q (Pos-rec FP i M h b (f q) pos)

  -- Initial algebra proof

  -- This is in from our paper or α from Prop 5.3
  ini : Σ (Σ S (λ s → Q s → W S Q))
           (λ {(s , f) → ((i : Ind) → P i s → X i) × ((i : Ind) (q : Q s) → Pos WAlg i (f q) → X i)}) →
        Σ (W S Q) (λ w → (i : Ind) → Pos WAlg i w → X i)  
  ini ((s , f) , (g , h)) = sup-W s f , λ i → λ {(here p) → g i p ; (below q b) → h i q b}

  -- This is α̅ from our paper or β̅ in Prop 5.3
  α̅ : Σ (W S Q) (λ w → (i : Ind) → Pos WAlg i w → X i) → Y
  α̅ (w , k) = W-rec S Q (λ w → ((i : Ind) → Pos WAlg i w → X i) → Y)
                  (λ {s'} {f'} r' k' → α (s' , (λ i p → k' i (here p)) , λ q → r' q (λ i b → k' i (below q b))))
                  w k
  {- Agda complains about the below
  α' (sup-W s f , k) = α (s , g , λ q → α' (f q , λ i → h i q))
    where
      g : (i : Ind) → P i s → X i
      g i p = k i (here s f p)
      
      h : (i : Ind) → (q : Q s) → Pos WAlg i (f q) → X i
      h i q b = k i (below s f q b)
  -}                  

  -- Diagram commutes 
  α̅-comm : (s : S) (f : Q s → W S Q) (g : (i : Ind) → P i s → X i) (h : (i : Ind) (q : Q s) → Pos WAlg i (f q) → X i) →
           α̅ (ini ((s , f) , (g , h))) ≡ α (s , g , λ q → α̅ (f q , λ i → h i q))
  α̅-comm s f g h = refl      

  -- Terminal coalgebra proof

  -- This is out from our paper or α⁻¹ in Prop 5.4
  out : Σ (M S Q) (λ m → (i : Ind) → Pos MAlg i m → X i) →
        Σ (Σ S (λ s → Q s → M S Q))
          (λ {(s , f) → ((i : Ind) → P i s → X i) × ((i : Ind) (q : Q s) → Pos MAlg i (f q) → X i)})
  out (m , k) = (shape m , pos m) , (g₁ , g₂)
    where
      g₁ : (i : Ind) → P i (shape m) → X i
      g₁ i p = k i (transport (cong (Pos MAlg i) (M-eta-eq m)) (here p))

      g₂ : (i : Ind) (q : Q (shape m)) → Pos MAlg i (pos m q) → X i
      g₂ i q b = k i (transport (cong (Pos MAlg i) (M-eta-eq m)) (below q b))

  β̅₁ : Y → M S Q
  β̅₁ y = M-coiter S Q Y βs βh y
  {-
  shape (β̅₁ y) = βs y 
  pos (β̅₁ y) q = β̅₁ (βh y q)
  -}

  β̅₂ : (y : Y) → (i : Ind) → Pos MAlg i (β̅₁ y) → X i
  β̅₂ y i p = aux p (y , refl)
    where
      aux : Pos MAlg i (β̅₁ y) → Σ Y (λ y' → β̅₁ y' ≡ β̅₁ y) → X i
      aux = Pos-rec MAlg i (λ m → Σ Y (λ y → β̅₁ y ≡ m) → X i) h b (β̅₁ y) -- using initiality of Pos
        where
           h : {s : S} {f : Q s → Z MAlg} → P i s → Σ Y (λ y' → β̅₁ y' ≡ χ MAlg s f) → X i
           h {s} {f} p (y , eq) = βg y i (subst (P i) shape-eq p)
             where
               shape-eq : s ≡ shape (β̅₁ y)
               shape-eq = cong shape (sym eq)

           b : {s : S} {f : Q s → Z MAlg} (q : Q s) → (Σ Y (λ y₁ → β̅₁ y₁ ≡ f q) → X i) →
               Σ Y (λ y₁ → β̅₁ y₁ ≡ χ MAlg s f) → X i
           b {s} {f} q g (y , eq) =  g (βh y (transport pos-eq q) ,
                                     sym (funExt⁻Dep {A = λ i → pos-eq i}
                                                     {B = M S Q}
                                                     {transport pos-eq}
                                                     pos-eq
                                                     arg-path
                                                     {f = f} {g = pos (β̅₁ y)}
                                                     fun-path q)) 
             where
               shape-eq : s ≡ shape (β̅₁ y)
               shape-eq = cong shape (sym eq)

               pos-eq : Q s ≡ Q (βs y) 
               pos-eq = cong Q shape-eq

               fun-path : PathP (λ i → Q (shape-eq i) → M S Q) f (pos (β̅₁ y)) 
               fun-path = cong pos (sym eq)

               arg-path : (q : Q s) → PathP (λ i → pos-eq i) q (transport pos-eq q)
               arg-path q = (transport-filler pos-eq q)

               funExt⁻Dep : {A : I → Type} {B : Type ℓ} {transf : A i0 → A i1}
                            (shape-eq : A i0 ≡ A i1)
                            (fun-path : (a : A i0) → PathP (λ i → shape-eq i) a (transf a)) 
                            {f : (x : A i0) → B} {g : (x : A i1) → B}
                            → PathP (λ i → shape-eq i → B) f g
                            → ((x : shape-eq i0) → f x ≡ g (transf x))
               funExt⁻Dep shape-eq fun-path p x i = p i (fun-path x i)    

  -- This is β̅ from our paper or β̅ in Prop 5.4
  β̅ : Y → Σ (M S Q) (λ m → (i : Ind) → Pos MAlg i m → X i)
  β̅ y = β̅₁ y , β̅₂ y


  β̅-comm : (y : Y) → out (β̅ y) ≡ ((βs y , β̅₁ ∘ (βh y)) , (βg y , λ i q → β̅₂ (βh y q) i))
  β̅-comm y =
    ΣPathP (ΣPathP (refl , refl) , ΣPathP (funExt (λ i → funExt λ p → {!!}) , {!!})) -- TODO, this should use initiality of Pos 




