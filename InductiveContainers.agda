{-# OPTIONS --without-K --guardedness --cubical --rewriting #-}

open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Nat
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Path

-- Preamble

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

-- Lifting M to relations
record M-R {S : Set} {Q : S → Set} (R : M S Q → M S Q → Set) (m₀ m₁ : M S Q) : Set where
  field
   s-eq : shape m₀ ≡ shape m₁        
   p-eq : (q₀ : Q (shape m₀))(q₁ : Q (shape m₁))(q-eq : PathP (λ i → Q (s-eq i)) q₀ q₁)
          → R (pos m₀ q₀) (pos m₁ q₁)
open M-R

CoInd-M : {S : Set} {Q : S → Set} (R : M S Q → M S Q → Set)
          (is-bisim : {m₀ m₁ : M S Q} → R m₀ m₁ → M-R R m₀ m₁) {m₀ m₁ : M S Q} → R m₀ m₁ → m₀ ≡ m₁
shape (CoInd-M R is-bisim r i) = s-eq (is-bisim r) i
pos (CoInd-M {S} {Q} R is-bisim {m₀ = m₀}{m₁ = m₁} r i) q =
  CoInd-M R is-bisim {m₀ = pos m₀ q₀} {m₁ = pos m₁ q₁} (p-eq (is-bisim r) q₀ q₁ q₂) i
    where QQ : I → Set
          QQ i = Q (s-eq (is-bisim r) i)

          q₀ : QQ i0
          q₀ = transp (λ j → QQ (~ j ∧ i)) (~ i) q

          q₁ : QQ i1
          q₁ = transp (λ j → QQ (j ∨ i)) i q

          q₂ : PathP (λ i → QQ i) q₀ q₁
          q₂ k = transp (λ j → QQ ((~ k ∧ ~ j ∧ i) ∨ (k ∧ (j ∨ i)) ∨
                 ((~ j ∧ i) ∧ (j ∨ i)))) ((~ k ∧ ~ i) ∨ (k ∧ i)) q

-- we have (propositional) η equality for M in Cubical Agda
M-eta-eq : {S' : Set} {Q' : S' → Set} (m : M S' Q') → sup-M (shape m) (pos m) ≡ m
shape (M-eta-eq m i) = shape m
pos (M-eta-eq m i) = pos m

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
  open Iso

  record ContFuncIso (S : Set) (P : S → Set) : Set₁ where
    constructor iso
    field
      Z : Set
      χ : Iso (Σ[ s ∈ S ] (P s → Z)) Z

  open ContFuncIso

  WAlg : ContFuncIso S Q
  WAlg = iso (W S Q) isom
    where
      isom : Iso (Σ S (λ s → Q s → W S Q)) (W S Q)
      Iso.fun isom = uncurry sup-W
      Iso.inv isom (sup-W s f) = s , f
      Iso.rightInv isom (sup-W s f) = refl
      Iso.leftInv isom (s , f) = refl

  MAlg : ContFuncIso S Q
  MAlg = iso (M S Q) isom
    where
      isom : Iso (Σ S (λ s → Q s → M S Q)) (M S Q)
      Iso.fun isom = uncurry sup-M
      Iso.inv isom m = shape m , pos m
      Iso.rightInv isom m = M-eta-eq m
      Iso.leftInv isom (s , f) = refl

  data Pos (FP : ContFuncIso S Q) (i : Ind) : Z FP → Set where
    here : {wm : FP .Z} → P i (fst (FP .χ .inv wm)) → Pos FP i wm
    below : {wm : FP .Z} → (q : Q (fst (FP .χ .inv wm))) → Pos FP i (snd (FP .χ .inv wm) q) →
            Pos FP i wm

  Pos-rec : (FP : ContFuncIso S Q) (i : Ind) (M : (z : Z FP) → Pos FP i z → Set)
            (h : {wm : FP .Z} (p : P i (fst (FP .χ .inv wm))) → M wm (here p))
            (b : {wm : FP .Z} (q : Q (fst (FP .χ .inv wm))) {b : Pos FP i (snd (FP .χ .inv wm) q)}
            → M (snd (FP .χ .inv wm) q) b → M wm (below q b)) →
            (z : Z FP) (pos : Pos FP i z) → M z pos
  Pos-rec FP i M h b z (here p) = h p
  Pos-rec FP i M h b z (below {wm} q pos) = b q (Pos-rec FP i M h b (snd (FP .χ .inv wm) q) pos)

  -- Initial algebra proof

  -- This is into from our paper or α from Prop 5.3
  into : Σ (Σ S (λ s → Q s → W S Q))
           (λ {(s , f) → ((i : Ind) → P i s → X i) ×
           ((i : Ind) (q : Q s) → Pos WAlg i (f q) → X i)}) →
         Σ (W S Q) (λ w → (i : Ind) → Pos WAlg i w → X i)  
  into ((s , f) , (g , h)) = sup-W s f , λ i → λ {(here p) → g i p ; (below q b) → h i q b}

  α̅' : (w : W S Q) → ((i : Ind) → Pos WAlg i w → X i) → Y
  α̅' (sup-W s f) k = α (s , g , λ q → α̅' (f q)  (λ i → h i q))
    where
      g : (i : Ind) → P i s → X i
      g i p = k i (here p)
      
      h : (i : Ind) → (q : Q s) → Pos WAlg i (f q) → X i
      h i q b = k i (below q b)

  -- This is α̅ from our paper or β̅ in Prop 5.3
  α̅ : Σ (W S Q) (λ w → (i : Ind) → Pos WAlg i w → X i) → Y
  α̅ (w , k) = α̅' w k

  -- Diagram commutes 
  α̅-comm : (s : S) (f : Q s → W S Q) (g : (i : Ind) → P i s → X i)
           (h : (i : Ind) (q : Q s) → Pos WAlg i (f q) → X i) →
           α̅ (into ((s , f) , (g , h))) ≡ α (s , g , λ q → α̅ (f q , λ i → h i q))
  α̅-comm s f g h = refl

  -- α̅ is unique
  α̅-unique : (α̃ : Σ (W S Q) (λ w → (i : Ind) → Pos WAlg i w → X i) → Y) →
             ((s : S) (f : Q s → W S Q) (g : (i : Ind) → P i s → X i)
             (h : (i : Ind) (q : Q s) → Pos WAlg i (f q) → X i) →
             α̃ (into ((s , f) , (g , h))) ≡ α (s , g , λ q → α̃ (f q , λ i → h i q))) →
             α̅ ≡ α̃
  α̅-unique α̃ α̃-comm = funExt w-rec
    where
      lemma : (s : S) (f : Q s → W S Q) (g : (i : Ind) → Pos WAlg i (sup-W s f) → X i) →
              α̃ (into ((s , f) , (λ i p → g i (here p)) , (λ i q b → g i (below q b)))) ≡
              α̃ (sup-W s f , g)
      lemma s f g = cong₂ (λ w fun → α̃ (w , fun)) refl (funExt λ i → funExt (λ {(here p) → refl ; (below q b) → refl})) 

      w-rec : (x : Σ (W S Q) (λ w → (i : Ind) → Pos WAlg i w → X i)) → α̅ x ≡ α̃ x
      w-rec (sup-W s f , k) = W-rec S Q
                               (λ w → (k : (i : Ind) → Pos WAlg i w → X i) → α̅ (w , k) ≡ α̃ (w , k))
                               (λ {s'} {f'} ind k →
                                 (λ i → α (s' , (λ i p → k i (here p)) ,
                                        λ q → ind q (λ i pos → k i (below q pos)) i)) ∙
                                 sym (α̃-comm s' f' (λ i p → k i (here p))
                                   (λ i q b → k i (below q b))) ∙
                                 lemma s' f' k)
                               (sup-W s f) k

  -- Terminal coalgebra proof

  -- This is out from our paper or α⁻¹ in Prop 5.4
  out : Σ (M S Q) (λ m → (i : Ind) → Pos MAlg i m → X i) →
        Σ (Σ S (λ s → Q s → M S Q))
          (λ {(s , f) → ((i : Ind) → P i s → X i) ×
          ((i : Ind) (q : Q s) → Pos MAlg i (f q) → X i)})
  out (m , k) = (shape m , pos m) , ((λ i p → k i (here p)) , (λ i q p → k i (below q p)))

  β̅₁ : Y → M S Q
  shape (β̅₁ y) = βs y 
  pos (β̅₁ y) = β̅₁ ∘ (βh y) 

  β̅₂ : (y : Y) → (i : Ind) → Pos MAlg i (β̅₁ y) → X i
  β̅₂ y i (here p) = βg y i p
  β̅₂ y i (below q p) = β̅₂ (βh y q) i p

  -- This is β̅ from our paper or β̅ in Prop 5.4
  β̅ : Y → Σ (M S Q) (λ m → (i : Ind) → Pos MAlg i m → X i)
  β̅ y = β̅₁ y , β̅₂ y

  β̅-comm : (y : Y) → out (β̅ y) ≡ ((βs y , β̅₁ ∘ (βh y)) , (βg y , λ i q → β̅₂ (βh y q) i))
  β̅-comm y = ΣPathP (refl , refl)

  β̅-unique : (β̃ : Y → Σ (M S Q) (λ m → (i : Ind) → Pos MAlg i m → X i)) → 
             ((y : Y) → out (β̃ y) ≡
                        ((βs y , λ q → fst (β̃ (βh y q))) , (βg y , λ i q → snd (β̃ (βh y q)) i))) →
             (y : Y) → β̃ y ≡ β̅ y
  β̅-unique β̃ comm y = ΣPathP (fst-eq , {!!}) -- TODO: second part of proof
    where
      data R : M S Q → M S Q → Set where
        R-intro : (y : Y) → R (fst (β̃ y)) (β̅₁ y)

      eq-pos : (y : Y) → PathP (λ i → (a : Q (fst (PathPΣ (fst (PathPΣ (comm y)))) i)) → M S Q)
                               (pos (fst (β̃ y))) (λ q → fst (β̃ (βh y q)))
      eq-pos y' = snd (PathPΣ (fst (PathPΣ (comm y'))))

      eq-pos-app : (y : Y)
                   {q0 : Q (fst (PathPΣ (fst (PathPΣ (comm y)))) i0)}
                   {q1 : Q (fst (PathPΣ (fst (PathPΣ (comm y)))) i1)} →
                   PathP (λ i → Q (fst (PathPΣ (fst (PathPΣ (comm y)))) i)) q0 q1 →
                   pos (fst (β̃ y)) q0 ≡ fst (β̃ (βh y q1))
      eq-pos-app y' q-eq i = eq-pos y' i (q-eq i)

      is-bisim-R : {m₀ : M S Q} {m₁ : M S Q} → R m₀ m₁ → M-R R m₀ m₁
      s-eq (is-bisim-R (R-intro y')) = fst (PathPΣ (fst (PathPΣ (comm y'))))
      p-eq (is-bisim-R (R-intro y')) q₀ q₁ q-eq =
        subst (λ X → R X (β̅₁ (βh y' q₁))) (sym (eq-pos-app y' q-eq)) (R-intro (βh y' q₁))

      fst-eq : fst (β̃ y) ≡ β̅₁ y
      fst-eq = CoInd-M {S} {Q} R is-bisim-R (R-intro y)

{-
      unique-s : (y : Y) → shape (fst (β̃ y)) ≡ shape (β̅₁ y)
      unique-s y = fst (PathPΣ (fst (PathPΣ (comm y))))

      unique-p : (y : Y) → PathP (λ i → Q (unique-s y i) → M S Q)
                                 (pos (fst (β̃ y))) (λ q → fst (β̃ (βh y q)))
      unique-p y = snd (PathPΣ (fst (PathPΣ (comm y))))

      thr-β̃-comm : (y : Y) → PathP (λ i → (ind : Ind) → P ind (unique-s y i) → X ind)
                                   (λ ind p → snd (β̃ y) ind (here p))
                                   (βg y)
      thr-β̃-comm y i = fst (snd (comm y i))

      fou-β̃-comm : (y : Y) →
                   PathP (λ i → (ind : Ind) → (q : Q (unique-s y i)) →
                          Pos MAlg ind ((unique-p y i) q) → X ind)
                         (λ ind q b → snd (β̃ y) ind (below q b))
                         (λ ind q → snd (β̃ (βh y q)) ind)
      fou-β̃-comm y i = snd (snd (comm y i))

      snd-eq : PathP (λ i → (ind : Ind) → Pos MAlg ind (fst-eq i) → X ind) (snd (β̃ y)) (β̅₂ y)
      snd-eq = {!!}
-}
