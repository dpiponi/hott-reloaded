{-# OPTIONS --without-K --type-in-type #-}

module Section-2-2-9 where

 import Section-2-2-1
 open Section-2-2-1
 open Paths

 import Section-2-2-2
 open Section-2-2-2

 import Section-2-2-3
 open Section-2-2-3

 import Section-2-2-4
 open Section-2-2-4

 import tools
 open tools

 open import Section-2-2-6
-- open Section-2-2-6

 open import Section-2-2-7
 open 2-7

 open import Section-2-2-8

 module 2-9 {A : Set} {B : A → Set} where

   happly : {f g : ((x : A) → B x)} → (f ≡ g) → (x : A) → f x ≡ g x
   happly refl x = refl

{- j (λ f g r → (x : A) → f x ≡ g x)
                    (λ f r → refl)
                    r-}

   postulate axiom-2-9-3 : {f g : ((x : A) → B x)} → isequiv (happly {f} {g})

   funext : {f g : ((x : A) → B x)} → ((x : A) → f x ≡ g x) → f ≡ g
   funext = pr₁ (isequiv-to-qinv happly axiom-2-9-3)

   computation : {f g : ((x : A) → B x)} → (r : (x : A) → f x ≡ g x) → happly (funext r) ≡ r
   computation = pr₁ (pr₂ (isequiv-to-qinv happly axiom-2-9-3))

   uniqueness : {f g : ((x : A) → B x)} → (r : f ≡ g) → funext (happly r) ≡ r
   uniqueness = pr₂ (pr₂ (isequiv-to-qinv happly axiom-2-9-3))

   refl∏ : (f : ((x : A) → B x)) → refl {_} {f} ≡ funext (λ x → refl {_} {f x})
   refl∏ f = refl {_} {f}                   ≡⟨ (uniqueness refl)⁻¹ ⟩
             funext (happly (refl {_} {f})) ≡⟨ ap funext refl ⟩        
             funext (λ x → refl {_} {f x})
             ▻

   ∏⁻¹ : {f g : ((x : A) → B x)} → (α : f ≡ g) → α ⁻¹ ≡ funext (λ x → (happly α x)⁻¹)
   ∏⁻¹ = j (λ f g α → α ⁻¹ ≡ funext (λ x → (happly α x)⁻¹))
             (λ f → (refl {_} {f})⁻¹  ≡⟨ (uniqueness refl)⁻¹ ⟩
                    funext (happly ((refl {_} {f}) ⁻¹)) ≡⟨ ap funext refl ⟩
                    funext (λ x → (happly (refl {(x₁ : A) → B x₁} {f}) x) ⁻¹)
                    ▻)
 
   ∏■ : {f g h : ((x : A) → B x)} → (α : f ≡ g) → (β : g ≡ h) → (α ■ β) ≡ funext (λ x → happly α x ■ happly β x)
   ∏■ = j₂ (λ f g h α β → (α ■ β) ≡ funext (λ x → happly α x ■ happly β x))
           (λ f → (refl {_} {f} ■ refl {_} {f}) ≡⟨ refl ⟩
                  refl {_} {f} ≡⟨ (uniqueness refl)⁻¹ ⟩
                  funext (happly (refl {_} {f})) ≡⟨ ap funext refl ⟩
                  funext (λ x → happly (refl {_} {f}) x ■ happly (refl {_} {f}) x)
                  ▻)

 open 2-9

 module theorem-2-9-4 {X : Set} {A B : X → Set} where

   A→B = λ x → A x → B x

   theorem-2-9-4 : {x₁ x₂ : X} → (p : x₁ ≡ x₂) →  (f : A x₁ → B x₁)
                   → transport A→B p f ≡ λ z → transport B p (f (transport A (p ⁻¹) z))
   theorem-2-9-4 refl = λ x → refl

 open theorem-2-9-4

 module theorem-2-9-5 {X : Set} {A : X → Set} {B : (x : X) → A x → Set} where

   Π : X → Set
   Π = λ x → (a : A x) → B x a

   B^ : (∑ X A) → Set
   B^ = λ w → B (pr₁ w) (pr₂ w)

   theorem-2-9-5 : {x₁ x₂ : X} → (p : x₁ ≡ x₂) → (f : (a : A x₁) → B x₁ a) → (a : A x₂) →
                   transport Π p f a ≡
                   transport B^ 
                             ((2-7-2.pair= {_} {_} {_ , _} {_ , _} ((p ⁻¹) , refl {_} {transport A (p ⁻¹) a}))⁻¹)
                             (f (transport A (p ⁻¹) a))
   theorem-2-9-5 refl x a = refl


 module lemma-2-9-6 {X : Set} {A B : X → Set} where

   lemma-2-9-6 : {x y : X} {p : x ≡ y} → (f : A x → B x) → (g : A y → B y)
                           → (transport _ p f ≡ g) ≃ ((a : A x) → (transport _ p (f a) ≡ g (transport _ p a)))
   lemma-2-9-6 {x} {.x} {refl} _ _ = (happly , axiom-2-9-3)

   hat : {x y : X} {p : x ≡ y} (f : A x → B x) → (g : A y → B y)
                           → (transport _ p f ≡ g) → ((a : A x) → (transport _ p (f a) ≡ g (transport _ p a)))
   hat {x} {.x} {refl} _ _ = happly

   proof : {x y : X} {p : x ≡ y} (f : A x → B x) → (g : A y → B y) → (a : A x) → (q : transport _ p f ≡ g)
              → (transport (λ x → A x → B x) p f) (transport A p a) ≡ g (transport A p a)
   proof {x} {y} {p} f g a q = (transport (λ x → A x → B x) p f) (transport A p a)
                                   ≡⟨ ap {(x₁ : A y) → B y} (λ h → h (transport A p a)) (theorem-2-9-4 p f) ⟩
                 transport B p (f (transport A (p ⁻¹) (transport A p a)))
                                   ≡⟨ ap (λ Q → transport B p (f Q)) (lemma-2-3-9 {X} {A} x y x (p) (p ⁻¹) a) ⟩
                 transport B p (f (transport A (p ■ (p ⁻¹)) a))
                                   ≡⟨ ap (λ Q → transport B p (f (transport A Q a))) (p■p⁻¹≡refl p) ⟩
                 hat {x} {y} {p} f g q a

   theorem : {x y : X} {p : x ≡ y} → (f : A x → B x) → (g : A y → B y) → (a : A x) → (q : transport _ p f ≡ g)
             → happly q (transport _ p a) ≡ proof {x} {y} {p} f g a q
   theorem {x} {.x} {refl} f g a q = hat {x} {x} {refl} f g q a
                                         ≡⟨ p≡refl■p _ ⟩
                              (ap (λ Q → transport B refl (f (transport A Q a))) (p■p⁻¹≡refl refl)) ■ happly q a
                                         ≡⟨ p≡refl■p _ ⟩
                              ap (λ Q → transport B refl (f Q)) (lemma-2-3-9 {X} {A} x x x (refl) (refl ⁻¹) a) ■ refl ■ happly q a
                                         ≡⟨ p≡refl■p _ ⟩
                              ap (λ h → h (transport A refl a))
                                 (theorem-2-9-4 (refl {_} {g a}) f) ■ refl {_} {f a} ■ refl {_} {f a} ■ happly q (a)
                              ▻

 module lemma-2-9-7 {X : Set} {A : X → Set} {B : (x : X) → A x → Set} where

   B^ : (∑ X A) → Set
   B^ = λ w → B (pr₁ w) (pr₂ w)
   F = λ z → (x : A z) → B z x
   fibresection = λ x → (a : A x) → B x a

   compute : {x y : X} → (p : x ≡ y) → (f : fibresection x) → (g : fibresection y) →
                          (transport F p f ≡ g) →
                          (a : A x) → transport B^ (2-7-2.pair= {X} {A} {x , a} {y , (p ∗) a} (p , refl)) (f a) ≡ g ((p ∗) a)
   compute refl f g = happly

   unique : {x y : X} → (p : x ≡ y) → (f : fibresection x) → (g : fibresection y) →
                    (((a : A x) → transport B^ (2-7-2.pair= {X} {A} {x , a} {y , (p ∗) a} (p , refl)) (f a) ≡ g ((p ∗) a))
                    → transport F p f ≡ g)
   unique refl f g = funext

   -- XXX Come back here
   forward : {x y : X} → (p : x ≡ y) → (f : fibresection x) → (g : fibresection y) →
              (r : ((a : A x) → transport B^ (2-7-2.pair= {X} {A} {x , a} {y , transport A p a} (p , refl)) (f a) ≡ g ((p ∗) a))) → compute p f g (unique p f g r) ≡ r 
   forward refl f g = computation

   backward : {x y : X} → (p : x ≡ y) → (f : fibresection x) → (g : fibresection y) →
                                          (r : transport F p f ≡ g) → unique p f g (compute p f g r) ≡ r 
   backward refl f g = uniqueness

   lemma-2-9-7 : (x y : X) → (p : x ≡ y) → (f : fibresection x) → (g : fibresection y) →
                    (transport F p f ≡ g) ≃
                    ((a : A x) → transport B^ (2-7-2.pair= {X} {A} {x , a} {y , (p ∗) a} (p , refl {A y} {(p ∗) a})) (f a) ≡ g ((p ∗) a))
   lemma-2-9-7 = λ x y p f g → (compute p f g , qinv-to-isequiv (compute p f g) (unique p f g , forward p f g , backward p f g))
