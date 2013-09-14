{-# OPTIONS --without-K --type-in-type #-}

module Section-2-2-11 where

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

 module 2-out-of-6 {A B C D : Set} (f : A → B) (g : B → C) (h : C → D) (q : isequiv (g ○ f)) (r : isequiv (h ○ g)) where
   q' : qinv (g ○ f)
   q' = isequiv-to-qinv (g ○ f) q
   
   a : C → A
   a = pr₁ q'

   α : (g ○ (f ○ a)) ~ id
   α = pr₁ (pr₂ q')

   β : (a ○ (g ○ f)) ~ id
   β = pr₂ (pr₂ q')

   r' : qinv (h ○ g)
   r' = isequiv-to-qinv (h ○ g) r
   
   b : D → B
   b = pr₁ r'

   γ : (h ○ (g ○ b)) ~ id
   γ = pr₁ (pr₂ r')

   δ : (b ○ (h ○ g)) ~ id
   δ = pr₂ (pr₂ r')

   f-has-right-inverse : (f ○ (a ○ g)) ~ id
   f-has-right-inverse x = f (a (g x)) ≡⟨ (δ (f (a (g x))))⁻¹ ⟩
             b (h (g (f (a (g x))))) ≡⟨ ap (b ○ h) (α (g x)) ⟩
             b (h (g x)) ≡⟨ δ x ⟩
             x
             ▻

   f-has-qinv : qinv f
   f-has-qinv = (a ○ g , f-has-right-inverse , β)

   f-is-equiv : isequiv f
   f-is-equiv = qinv-to-isequiv f f-has-qinv

 module homotopic-to-equiv {A B : Set} (f : A → B) (g : A ≃ B) (H : f ~ pr₁ g) where
   g₀ : A → B
   g₀ = pr₁ g

   g' : qinv g₀
   g' = isequiv-to-qinv g₀ (pr₂ g)

   h : B → A
   h = pr₁ g'

   α : (g₀ ○ h) ~ id
   α = pr₁ (pr₂ g')

   β : (h ○ g₀) ~ id
   β = pr₂ (pr₂ g')

   is-equiv : isequiv f
   is-equiv = qinv-to-isequiv f (h , (λ x → H (h x) ■ α x) , (λ x → ap h (H x) ■ β x))

 module 2-11 where

   module theorem-2-11-1 {A B : Set} (f : A ≃ B) {a a' : A} where
     
     f₀ : A → B
     f₀ = pr₁ f

     q : qinv f₀
     q = isequiv-to-qinv f₀ (pr₂ f)

     f⁻¹ : B → A
     f⁻¹ = pr₁ q

     α : (b : B) → f₀ (f⁻¹ b) ≡ b
     α = pr₁ (pr₂ q) 

     β : (a : A) → f⁻¹ (f₀ a) ≡ a
     β = pr₂ (pr₂ q) 

     concat : {A : Set} {a a' b b' : A} (α' : b ≡ a) → (β : a' ≡ b') → (a ≡ a') → (b ≡ b')
     concat α' β p = α' ■ p ■ β

     conc'' : {A : Set} {a a' b b' : A} (α : a ≡ b) → (β : a' ≡ b') → (p : a ≡ a') → (b ≡ b')
     conc'' one two p = (one ⁻¹) ■ p ■ two

     concat' : {A : Set} {a a' b b' : A} (α : a ≡ b) → (β' : b' ≡ a') → (b ≡ b') → (a ≡ a')
     concat' α β' q = α ■ q ■ β'

     conc' : {A : Set} {a a' b b' : A} (α : a ≡ b) → (β : a' ≡ b') → (p : b ≡ b') → (a ≡ a')
     conc' one two p = one ■ p ■ (two ⁻¹)

     myequiv : {A : Set} {a a' b b' : A} (α : a ≡ b) → (α' : b ≡ a) → (β : a' ≡ b') → (β' : b' ≡ a') →
               (q : b ≡ b')
               → ({d : A} (q : b ≡ d) → α' ■ (α ■ q) ≡ q)
               → ({d : A} (q : d ≡ b') → q ■ (β' ■ β) ≡ q)
               → concat α' β (concat' α β' q) ≡ q
     myequiv α α' β β' q lcancel rcancel = α' ■ (α ■ q ■ β') ■ β ≡⟨ ■-assoc α' (α ■ q ■ β') β ⟩
                          (α' ■ (α ■ (q ■ β'))) ■ β ≡⟨ lcancel (q ■ β') ■r β ⟩
                          (q ■ β') ■ β ≡⟨ (■-assoc q β' β)⁻¹ ⟩
                          q ■ (β' ■ β) ≡⟨ rcancel q ⟩
                           q ▻

     isequiv-odd : {A : Set} {a a' b b' : A} (α : a ≡ b) → (β : a' ≡ b') → (q : b ≡ b')
               → concat (α ⁻¹) β (concat' α (β ⁻¹) q) ≡ q
     isequiv-odd one two p = myequiv one (one ⁻¹) two (two ⁻¹) p (λ p → p⁻¹■p■q≡q one p) (λ p → p■q⁻¹■q≡p p two)

     isequiv-even : {A : Set} {a a' b b' : A} (α : a ≡ b) → (β : a' ≡ b') → (q : a ≡ a')
               → concat (α) (β ⁻¹) (concat' (α ⁻¹) (β ) q) ≡ q
     isequiv-even one two q = myequiv (one ⁻¹) one (two ⁻¹) two q (λ p → p■p⁻¹■q≡q one p) (λ p → p■q■q⁻¹≡p p two)

     concat-is-qinv : {A : Set} {a a' b b' : A} (α : a ≡ b) → (β : a' ≡ b') → qinv (conc' α β)
     concat-is-qinv one two = conc'' one two , (isequiv-even one two , isequiv-odd one two)

     concat-is-equiv : {A : Set} {a a' b b' : A} (α : a ≡ b) → (β : a' ≡ b') → isequiv (conc' α β)
     concat-is-equiv one two = qinv-to-isequiv (conc' one two) (concat-is-qinv one two)

     ap-homotopic-concat : (ap f⁻¹ ○ ap f₀) ~ (conc' (β a) (β a'))
     ap-homotopic-concat p = (ap f⁻¹ ○ ap f₀) p ≡⟨ (ap-hom-first f₀ f⁻¹ p) ⟩
                             ap (f⁻¹ ○ f₀) p ≡⟨ p≡p■q■q⁻¹ _ (β a') ⟩
                             ap (f⁻¹ ○ f₀) p ■ β a' ■ (β a')⁻¹ ≡⟨ ■-assoc (ap (f⁻¹ ○ f₀) p) (β a') ((β a')⁻¹) ⟩
                             (ap (f⁻¹ ○ f₀) p ■ β a') ■ (β a')⁻¹ ≡⟨ ((hom-square (f⁻¹ ○ f₀) id β p)⁻¹) ■r (β a' ⁻¹) ⟩
                             (β a ■ ap id p) ■ (β a')⁻¹ ≡⟨ (β a ■l ap-id-first p) ■r ((β a')⁻¹) ⟩
                             (β a ■ p) ■ (β a')⁻¹ ≡⟨ (■-assoc (β a) p _)⁻¹ ⟩
                             β a ■ p ■ (β a')⁻¹
                             ▻

     ap-homotopic-concat' : (ap f₀ ○ ap f⁻¹) ~ (conc' (α (f₀ a)) (α (f₀ a')))
     ap-homotopic-concat' q = (ap f₀ ○ ap f⁻¹) q ≡⟨ (ap-hom-first f⁻¹ f₀ q) ⟩
                             ap (f₀ ○ f⁻¹) q ≡⟨ p≡p■q■q⁻¹ _ (α (f₀ a')) ⟩
                             ap (f₀ ○ f⁻¹) q ■ α (f₀ a') ■ α (f₀ a')⁻¹ ≡⟨ ■-assoc (ap (f₀ ○ f⁻¹) q) (α (f₀ a')) (α (f₀ a')⁻¹) ⟩
                             (ap (f₀ ○ f⁻¹) q ■ α (f₀ a')) ■ α (f₀ a')⁻¹ ≡⟨ ((hom-square (f₀ ○ f⁻¹) id α q)⁻¹) ■r (α (f₀ a')⁻¹) ⟩
                             (α (f₀ a) ■ ap id q) ■ α (f₀ a')⁻¹ ≡⟨ (α (f₀ a) ■l ap-id-first q) ■r ((α (f₀ a'))⁻¹) ⟩
                             (α (f₀ a) ■ q) ■ α (f₀ a')⁻¹ ≡⟨ (■-assoc (α (f₀ a)) q _)⁻¹ ⟩
                             α (f₀ a) ■ q ■ (α (f₀ a'))⁻¹
                             ▻

     res₁ : isequiv (ap f⁻¹ ○ ap f₀ {a} {a'})
     res₁ = homotopic-to-equiv.is-equiv (ap f⁻¹ ○ ap f₀) ((conc' (β a) (β a')) , concat-is-equiv (β a) (β a')) ap-homotopic-concat

     res₂ : isequiv (ap f₀ ○ ap f⁻¹ {f₀ a} {f₀ a'})
     res₂ = homotopic-to-equiv.is-equiv (ap f₀ ○ ap f⁻¹) ((conc' (α (f₀ a)) (α (f₀ a'))) , (concat-is-equiv (α (f₀ a)) (α (f₀ a')))) ap-homotopic-concat'

     proof : isequiv (ap f₀ {a} {a'})
     proof = f-is-equiv (ap f₀) (ap f⁻¹) (ap f₀) res₁ res₂
                       where open 2-out-of-6

{-
     module X {a : A} {p : a ≡ a} {u : ap f₀ p ≡ refl} where

       inv-refl : p ≡ refl
       inv-refl = p ≡⟨ p≡refl■p ⟩
            refl ■ p ≡⟨ ap (λ Q → Q ■ p) (p⁻¹■p≡refl (β a))⁻¹ ⟩
            ((β a)⁻¹ ■ β a) ■ p ≡⟨ (■-assoc ((β a)⁻¹) (β a) p)⁻¹ ⟩
            (β a)⁻¹ ■ (β a ■ p) ≡⟨ ap (λ Q → (β a)⁻¹ ■ β a ■ Q) ((ap-id-first p)⁻¹) ⟩
            (β a)⁻¹ ■ (β a ■ ap id p) ≡⟨ ap (λ Q → (β a)⁻¹ ■ Q) (hom-square (f⁻¹ ○ f₀) id β p) ⟩
            (β a)⁻¹ ■ (ap (f⁻¹ ○ f₀) p ■ β a) ≡⟨ ap (λ Q → (β a)⁻¹ ■ Q ■ β a) ((ap-hom-first f₀ f⁻¹ p)⁻¹) ⟩
            (β a)⁻¹ ■ (ap f⁻¹ (ap f₀ p) ■ β a) ≡⟨ ap (λ Q → (β a)⁻¹ ■ (ap f⁻¹ Q ■ β a)) u ⟩
            (β a)⁻¹ ■ (refl ■ β a) ≡⟨ ap (λ Q → (β a)⁻¹ ■ Q) (p≡refl■p ⁻¹) ⟩
            (β a)⁻¹ ■ β a ≡⟨ p⁻¹■p≡refl (β a) ⟩
            refl
            ▻
     open X

     module Y {a : A} {p : a ≡ a} {q : a ≡ a} {u v : ap f₀ p ≡ ap f₀ q} where

       r1 : ap f₀ (p ■ q ⁻¹) ≡ refl
       r1 = ap f₀ (p ■ q ⁻¹) ≡⟨ ap-hom-second f₀ p (q ⁻¹) ⟩
            ap f₀ p ■ ap f₀ (q ⁻¹) ≡⟨ ap (λ Q → ap f₀ p ■ Q) (ap-inv-second f₀ q) ⟩
            ap f₀ p ■ (ap f₀ q)⁻¹ ≡⟨ ap (λ Q → ap f₀ p ■ (Q ⁻¹)) (v ⁻¹) ⟩
            ap f₀ p ■ (ap f₀ p)⁻¹ ≡⟨ p■p⁻¹≡refl (ap f₀ p) ⟩
            refl
            ▻

       r2 : p ■ q ⁻¹ ≡ refl
       r2 = X.inv-refl {a} {p ■ q ⁻¹} {r1} 

-}

 lemma-2-11-2-i : {A : Set} (a x₁ x₂ : A) → (p : x₁ ≡ x₂) → (q : a ≡ x₁) → transport (λ x → a ≡ x) p q ≡ q ■ p
 lemma-2-11-2-i a .a .a refl refl = refl

 lemma-2-11-2-ii : {A : Set} (a x₁ x₂ : A) → (p : x₁ ≡ x₂) → (q : x₁ ≡ a) → transport (λ x → x ≡ a) p q ≡ p ⁻¹ ■ q
 lemma-2-11-2-ii a .a .a refl refl = refl

 lemma-2-11-2-iii : {A : Set} (x₁ x₂ : A) → (p : x₁ ≡ x₂) → (q : x₁ ≡ x₁) → transport (λ x → x ≡ x) p q ≡ p ⁻¹ ■ q ■ p
 lemma-2-11-2-iii x₁ .x₁ refl q = q ≡⟨ p≡p■refl _ ⟩
                                 q ■ refl ≡⟨ p≡refl■p _ ⟩
                                 refl ■ q ■ refl
                                 ▻

{-
  lemma-2-3-10 : {A B : Set} → (f : A → B) → (P : B → Set) → {x y : A} → (p : x ≡ y) → (u : P (f x))
                             → transport (P ○ f) p u ≡ transport P (ap f p) u

-}

 theorem-2-11-3 : {A B : Set} (f g : A → B) → (a a' : A) → (p : a ≡ a') → (q : f a ≡ g a)
                      → transport (λ x → f x ≡ g x) p q ≡ (ap f p)⁻¹ ■ q ■ ap g p
 theorem-2-11-3 f g a .a refl q = q ≡⟨ p≡p■refl _ ⟩
                                 q ■ refl ≡⟨ p≡refl■p _ ⟩
                                 refl ■ q ■ refl
                                 ▻

 -- (p ∗) (f a) ≡ (p ∗) (g a)
 theorem-2-11-4 : {A : Set} (B : A → Set) (f g : (x : A) → B x) → {a a' : A} → (p : a ≡ a') → (q : f a ≡ g a)
                      → transport (λ x → f x ≡ g x) p q ≡ (apd f p)⁻¹ ■ ap (transport B p) q ■ apd g p
 theorem-2-11-4 B f g refl q = q ≡⟨ (apidp≡p q)⁻¹ ⟩
                              ap id q ≡⟨ p≡p■refl _ ⟩
                              ap id q ■ refl ≡⟨ p≡refl■p _ ⟩
                              refl ■ ap id q ■ refl
                              ▻

{-
?0 : ∑ q ≡ r → q ■ refl ≡ refl ■ r) isequiv
-}

 module theorem-2-11-5-refl {A : Set} {a : A} (q : a ≡ a) (r : a ≡ a) where

   forward : (q ≡ r) → (q ■ refl ≡ refl ■ r)
   forward p = p■refl≡p q ■ p ■ p≡refl■p r

   reverse : (q ■ refl ≡ refl ■ r) → (q ≡ r)
   reverse p = p≡p■refl q ■ p ■ refl■p≡p r

   hom1 : (x : q ■ refl ≡ refl ■ r) → forward (reverse x) ≡ x
   hom1 p = p■refl≡p q ■ (p≡p■refl q ■ p ■ refl■p≡p r) ■ p≡refl■p r
                     ≡⟨ ■-assoc (p■refl≡p q) _ (p≡refl■p r) ⟩
            (p■refl≡p q ■ (p≡p■refl q ■ p ■ refl■p≡p r)) ■ p≡refl■p r
                     ≡⟨ p⁻¹■p■q≡q (p≡p■refl q) _ ■r p≡refl■p r ⟩
            (p ■ refl■p≡p r) ■ p≡refl■p r
                     ≡⟨ (■-assoc p _ _)⁻¹ ⟩
            p ■ refl■p≡p r ■ p≡refl■p r
                     ≡⟨ p■q⁻¹■q≡p p (p≡refl■p r) ⟩
            p
            ▻

   hom2 : (x : q ≡ r) → reverse (forward x) ≡ x
   hom2 p = p≡p■refl q ■ (p■refl≡p q ■ p ■ p≡refl■p r) ■ refl■p≡p r ≡⟨ ■-assoc (p≡p■refl q) _ (refl■p≡p r) ⟩
            (p≡p■refl q ■ p■refl≡p q ■ p ■ p≡refl■p r) ■ refl■p≡p r ≡⟨ (p■p⁻¹■q≡q (p≡p■refl q) _) ■r refl■p≡p r ⟩
            (p ■ p≡refl■p r) ■ refl■p≡p r ≡⟨ (■-assoc p _ _)⁻¹ ⟩
            p ■ p≡refl■p r ■ refl■p≡p r ≡⟨ p■q■q⁻¹≡p p (p≡refl■p r) ⟩
            p
            ▻

   proof : (q ≡ r) ≃ (q ■ refl ≡ refl ■ r)
   proof = forward , qinv-to-isequiv forward (reverse , (hom1 , hom2))

   

 theorem-2-11-5 : {A : Set} {a a' : A} (p : a ≡ a') → (q : a ≡ a) → (r : a' ≡ a')
                            → (transport (λ x → x ≡ x) p q ≡ r) ≃ (q ■ p ≡ p ■ r)
 theorem-2-11-5 refl q r = proof
                           where open theorem-2-11-5-refl q r
