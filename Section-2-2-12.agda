{-# OPTIONS --without-K --type-in-type #-}

module Section-2-2-12 where

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

 open import Section-2-2-10
 open 2-10

 open import Section-2-2-11

 data void : Set where

 elim-void : {A : Set} → void → A
 elim-void ()

 data _+_ (A B : Set) : Set where
   inl : A → A + B
   inr : B → A + B

 based : {A : Set} {a : A} (C : (x : A) → a ≡ x → Set)
          → C a refl
          → (x : A) → (P : a ≡ x)
          → C x P
 based _ b _ refl = b

 module theorem-2-12-5 {A B : Set} {a₀ : A} where

{-
  code x = paths from base point to x
-}

   code : A + B → Set
   code (inl a) = a₀ ≡ a
   code (inr b) = void

   -- convert path to x to new rep
   encode : (x : A + B) → (p : inl a₀ ≡ x) → code x
   encode x p = transport code p (refl {_} {a₀})

   decode : (x : A + B) → (c : code x) → inl a₀ ≡ x
   decode (inl a) c = ap inl c
   decode (inr _) c = elim-void c

   proof₁ : (x : A + B) (p : inl a₀ ≡ x) → decode x (encode x p) ≡ p
   proof₁ x p = based {A + B} {inl a₀}
                (λ x p → decode x (encode x p) ≡ p)
                refl
                x p

   proof₂ : (x : A + B) (c : code x) → encode x (decode x c) ≡ c
   proof₂ (inl a) c = transport code (ap inl c) (refl {_} {a₀}) ≡⟨ (lemma-2-3-10 inl code c refl)⁻¹ ⟩
                      transport (λ a → a₀ ≡ a) c (refl {_} {a₀}) ≡⟨ lemma-2-11-2-i a₀ a₀ a c refl ⟩
                      refl {_} {a₀} ■ c ≡⟨ refl■p≡p c ⟩
                      c
                      ▻
   proof₂ (inr _) c = elim-void c

   proof : (x : A + B) → (inl a₀ ≡ x) ≃ code x
   proof x = encode x , qinv-to-isequiv (encode x) (decode x , (proof₂ x , proof₁ x))

 transport-coproduct-i : {X : Set} → {x₁ x₂ : X} → (p : x₁ ≡ x₂) → (A B : X → Set)
                            → (a : A x₁)
                            → transport (λ x → A x + B x) p (inl a) ≡ inl (transport A p a)
 transport-coproduct-i refl A B a = refl

 transport-coproduct-ii : {X : Set} → {x₁ x₂ : X} → (p : x₁ ≡ x₂) → (A B : X → Set)
                            → (b : B x₁)
                            → transport (λ x → A x + B x) p (inr b) ≡ inr (transport B p b)
 transport-coproduct-ii refl A B b = refl
