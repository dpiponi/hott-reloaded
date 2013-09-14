{-# OPTIONS --without-K --type-in-type #-}

module Section-2-2-10 where

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

 open import Section-2-2-9
 open 2-9
 open theorem-2-9-4

 module 2-10 where
   
   idtoeqv : {A B : Set} → (A ≡ B) → A ≃ B
   idtoeqv p = (p ∗ , f) where
      f : isequiv (transport (λ A → A) p) 
      f = j (λ A B p → isequiv (transport (λ A → A) p))
              (λ A → (id , (λ x → refl)) , id , (λ x → refl))
              p

   postulate axiom-2-10-3 : {A B : Set} → isequiv (idtoeqv {A} {B})

   ua : {A B : Set} → (A ≃ B) → (A ≡ B)
   ua = pr₁ (isequiv-to-qinv idtoeqv axiom-2-10-3)

   idtoeqv○ua≡id : {A B : Set} → (r : A ≃ B) → (idtoeqv ○ ua) r ≡ id r
   idtoeqv○ua≡id {A} {B} = pr₁ (pr₂ (isequiv-to-qinv idtoeqv axiom-2-10-3))

   ua○idtoeqv≡id : {A B : Set} → (ua {A} {B} ○ idtoeqv) ~ id
   ua○idtoeqv≡id {A} {B} = pr₂ (pr₂ (isequiv-to-qinv idtoeqv axiom-2-10-3))

   elim : {A B : Set} → (pr₁ ○ idtoeqv {A} {B}) ≡ transport (λ A → A)
   elim {A} {B} = funext (λ p → refl)

   -- Confusing 'cos book treats A ≃ B as if it's A → B.
   -- So need extra pr₁ on RHS
   unicomp : {A B : Set} → {f : A ≃ B} → {x : A} → transport {Set} (λ X → X) {A} {B} (ua f) x ≡ pr₁ f x
   unicomp {A} {B} {f} {x} = transport {Set} (λ X → X) {A} {B} (ua f) x ≡⟨ refl ⟩
                             pr₁ (idtoeqv (ua f)) x ≡⟨ ap (λ Q → pr₁ Q x) (idtoeqv○ua≡id f) ⟩
                             pr₁ f x
                             ▻

   unicomp' : {A B : Set} → (f : A ≃ B) → transport {Set} (λ X → X) {A} {B} (ua f) ≡ pr₁ f
   unicomp' {A} {B} f = transport {Set} (λ X → X) {A} {B} (ua f) ≡⟨ refl ⟩
                             pr₁ (idtoeqv (ua f)) ≡⟨ ap (λ Q → pr₁ Q) (idtoeqv○ua≡id f) ⟩
                             pr₁ f
                             ▻


   uniuniq : {A B : Set} → {p : A ≡ B} → p ≡ ua (idtoeqv p)
   uniuniq {A} {B} {p} = (ua○idtoeqv≡id p)⁻¹

   -- Identity of equivalence
   ide : {A : Set} → A ≃ A
   ide {A} = lemma-2-4-12i' A

   -- Composition of equivalence
   _○e_ : {A B C : Set} → (f : B ≃ C) → (f' : A ≃ B) → (A ≃ C)
   f ○e g = lemma-2-4-12iii g f

   _⁻¹e : {A B : Set} → A ≃ B → B ≃ A
   f ⁻¹e = lemma-2-4-12ii f

   refl≡uaid : {A : Set} → refl {Set} {A} ≡ ua ide
   refl≡uaid {A} = refl {Set} {A} ≡⟨ (ua○idtoeqv≡id refl)⁻¹ ⟩
                   ua (idtoeqv (refl {Set} {A})) ≡⟨ ap ua refl ⟩
                   ua ide
                   ▻

   -- Not quite method in book
   uafuag≡uafg-0 : {A B C : Set} → {p : A ≡ B} → {q : B ≡ C} → idtoeqv (p ■ q) ≡ idtoeqv q ○e idtoeqv p
   uafuag≡uafg-0 {A} {.A} {.A} {refl} {refl} = refl

   uafuag≡uafg : {A B C : Set} → {f : A ≃ B} → {g : B ≃ C} → ((ua f) ■ (ua g)) ≡ (ua (g ○e f))
   uafuag≡uafg {A} {B} {C} {f} {g} = ua f ■ ua g                ≡⟨ (ua○idtoeqv≡id (ua f ■ ua g))⁻¹ ⟩
                                     ua (idtoeqv (ua f ■ ua g)) ≡⟨ ap ua (uafuag≡uafg-0 {A} {B} {C} {ua f} {ua g}) ⟩
                                     ua (idtoeqv (ua g) ○e idtoeqv (ua f)) ≡⟨ ap (λ Q → ua (Q ○e idtoeqv (ua f))) (idtoeqv○ua≡id g) ⟩
                                     ua (g ○e idtoeqv (ua f)) ≡⟨ ap (λ Q → ua (g ○e Q)) (idtoeqv○ua≡id f) ⟩
                                     (ua (g ○e f))
                                     ▻

   uaf⁻1-0 : {A B : Set} → {f : A ≡ B} → idtoeqv (f ⁻¹) ≡ (idtoeqv f)⁻¹e
   uaf⁻1-0 {A} {.A} {refl} = refl

   uaf⁻1 : {A B : Set} → {f : A ≃ B} → ((ua f) ⁻¹) ≡ (ua (f ⁻¹e))
   uaf⁻1 {A} {B} {f} = (ua f) ⁻¹ ≡⟨ (ua○idtoeqv≡id ((ua f)⁻¹))⁻¹ ⟩
                       ua (idtoeqv ((ua f) ⁻¹)) ≡⟨ ap ua (uaf⁻1-0 {A} {B} {ua f}) ⟩
                       ua ((idtoeqv (ua f)) ⁻¹e) ≡⟨ ap (λ Q → ua (Q ⁻¹e)) (idtoeqv○ua≡id f) ⟩
                       ua (f ⁻¹e)
                       ▻
   
   lemma-2-10-5 : {A : Set} → {B : A → Set} → {x y : A} → {p : x ≡ y} → {u : B x}
                            → transport B p u ≡ pr₁ (idtoeqv (ap B p)) u
   lemma-2-10-5 {A} {B} {x} {y} {p} {u} =
                  transport (B ○ id) p u ≡⟨ lemma-2-3-10 B id p u ⟩
                  transport id (ap B p) u ≡⟨ refl ⟩
                  pr₁ (idtoeqv (ap B p)) u
                  ▻

 lcancel : {A : Set} → {x y z : A} → (p : x ≡ y) → (q : y ≡ z) →
           p ⁻¹ ■ p ■ q ≡ q
 lcancel {A} {x} {y} {z} p q = p ⁻¹ ■ p ■ q ≡⟨ ■-assoc (p ⁻¹) p q ⟩
                               (p ⁻¹ ■ p) ■ q ≡⟨ ap (λ Q → Q ■ q) (p⁻¹■p≡refl p) ⟩
                               refl ■ q ≡⟨ (p≡refl■p _)⁻¹ ⟩
                               q
                               ▻

