{-# OPTIONS --without-K --type-in-type #-}

 module Section-2-2-3 where

  import Section-2-2-1
  open Section-2-2-1
  open Paths

  import Section-2-2-2
  open Section-2-2-2

  -- Lemma 2.3.1

  transport : {A : Set} → (P : A → Set) → {x y : A} → (p : x ≡ y) → P x → P y
  transport P refl = id

  _∗ : {A : Set} → {P : A → Set} → {x y : A} → (p : x ≡ y) → P x → P y
  p ∗ = transport _ p

  -- dependent product

  data ∑ (A : Set) (B : A → Set) : Set where
    _,_ : (a : A) → B a → ∑ A B

  infixr 4 _,_

  pr₁ : {A : Set} {B : A → Set} → ∑ A B → A
  pr₁ (a , _) = a
  pr₂ : {A : Set} {B : A → Set} → (p : ∑ A B) → B (pr₁ p)
  pr₂ (_ , b) = b

  rec∑₀ : {A : Set} {B : A → Set} → {C : Set} → ((x : A) → B x → C) → (∑ A B) → C
  rec∑₀ f (a , b) = f a b

  rec∑₁ : {A : Set} {B : A → Set} → {C : Set} → ((x : A) → B x → C) → (∑ A B) → C
  rec∑₁ f x = f (pr₁ x) (pr₂ x)

  -- Path lifting property
  lift : {A : Set} → {P : A → Set} → {x y : A} → (u : P x) → (p : x ≡ y) → (x , u) ≡ (y , transport P p u)
  lift u refl = refl

  -- Lemma 2.3.4 (Dependent map)
  -- Generalisation of functoriality to dependent functions.
  apd : {A : Set} → {P : A → Set} → (f : (x : A) → P x) → {x y : A} → (p : x ≡ y) → (p ∗) (f x) ≡ f y
  apd f refl = refl

  -- Lemma 2.3.5
  -- Transport does obvious thing with constant fibres.

  transportconst : {A : Set} → {x y : A} → (B : Set) → (p : x ≡ y) → (b : B)
                 → transport (λ x → B) p b ≡ b
  transportconst B refl b = refl

 -- ap f p : f x ≡ f y
 -- transportconst B p (f x) : transport (λ x → B) p (f x) ≡ f x
 -- transportconst B p (f x) ■ ap f p : transport (λ x → B) p (f x) ■ f y
 -- apd f p : transport _ p (f x) ≡ f y
 -- Lift ends of p to f x and f y. Transport f x along p. You should get f y.
  lemma-2-3-8 : {A B : Set} → (f : A → B) → {x y : A} → (p : x ≡ y) → apd f p ≡ transportconst B p (f x) ■ ap f p
  lemma-2-3-8 f refl = refl

  lemma-2-3-9 : {A : Set} → {P : A → Set} → (x y z : A) → (p : x ≡ y) → (q : y ≡ z)
              → (u : P x) → (transport P q) ((transport P p) u) ≡ ((p ■ q)∗) u
  lemma-2-3-9 {A} {P} x .x .x refl refl u₁ = refl

  lemma-2-3-10 : {A B : Set} → (f : A → B) → (P : B → Set) → {x y : A} → (p : x ≡ y) → (u : P (f x))
                             → transport (P ○ f) p u ≡ transport P (ap f p) u
  lemma-2-3-10 f P refl u₁ = refl

  lemma-2-3-11 : {A : Set} → (P Q : A → Set) → {x y : A} → (f : (x : A) → P x → Q x) → (p : x ≡ y) → (u : P x)
                           → transport Q p (f x u) ≡ f y (transport P p u)
  lemma-2-3-11 {A} P Q f refl u = refl
