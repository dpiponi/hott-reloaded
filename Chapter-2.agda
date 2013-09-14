{-# OPTIONS --without-K --type-in-type #-}

module Chapter-2 where

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

 open import Section-2-2-12
 
 module Section-2-2-13 where
   open import Data.Nat

   code : ℕ → ℕ → Set
   code ℕ.zero ℕ.zero = unit
   code ℕ.zero (suc n) = void
   code (suc m) ℕ.zero = void
   code (suc m) (suc n) = code m n

   r : (n : ℕ) → code n n
   r ℕ.zero = ⋆
   r (suc n) = r n

   module theorem-2-13-1 where

     encode : (m n : ℕ) → (m ≡ n) → code m n
     encode m n p = transport (code m) p (r m)

     decode : (m n : ℕ) → code m n → m ≡ n
     decode zero zero x = refl {_} {zero}
     decode zero (suc n) x = elim-void x
     decode (suc m) zero x = elim-void x
     decode (suc m) (suc n) x = ap suc (decode m n x)

     proof₀ : (n : ℕ) → encode n n refl ≡ r n
     proof₀ n = refl

     proof₁ : (m n : ℕ) → (p : m ≡ n) → decode m n (encode m n p) ≡ p
     proof₁ zero .zero refl = refl
     proof₁ (suc n) .(suc n) refl = decode (suc n) (suc n) (r (suc n))
                                           ≡⟨ refl ⟩
                                    ap suc (decode n n (r (suc n)))
                                           ≡⟨ refl ⟩
                                    ap suc (decode n n (r n))
                                           ≡⟨ ap (ap suc) (proof₁ n n refl) ⟩
                                    ap suc refl
                                           ≡⟨ refl ⟩
                                    refl
                                    ▻
{-
  lemma-2-3-10 : {A B : Set} → (f : A → B) → (P : B → Set) → {x y : A} → (p : x ≡ y) → (u : P (f x))
                             → transport (P ○ f) p u ≡ transport P (ap f p) u

  lemma-2-11-2-ii : {A : Set} (a x₁ x₂ : A) → (p : x₁ ≡ x₂) → (q : x₁ ≡ a) → transport (λ x → x ≡ a) p q ≡ p ⁻¹ ■ q
  lemma-2-11-2-i : {A : Set} (a x₁ x₂ : A) → (p : x₁ ≡ x₂) → (q : a ≡ x₁) → transport (λ x → a ≡ x) p q ≡ q ■ p

  code ○ inl = λ a → a₀ ≡ a
  P = code
  f = inl
  P ○ f = λ a → a₀ ≡ a

-}

     proof₂ : (m n : ℕ) → (c : code m n) → encode m n (decode m n c) ≡ c
     proof₂ zero zero ⋆ = refl
     proof₂ zero (suc n) c = elim-void c
     proof₂ (suc m) zero c = elim-void c
     proof₂ (suc m) (suc n) c = encode (suc m) (suc n) (decode (suc m) (suc n) c)
                                       ≡⟨ refl ⟩
                                encode (suc m) (suc n) (ap suc (decode m n c))
                                       ≡⟨ refl ⟩
                                transport (code (suc m)) (ap suc (decode m n c)) (r (suc m))
                                       ≡⟨ (lemma-2-3-10 suc (code (suc m)) (decode m n c) (r (suc m)))⁻¹ ⟩
                                transport (λ x → code (suc m) (suc x)) (decode m n c) (r (suc m))
                                       ≡⟨ refl ⟩
                                transport (λ x → code m x) (decode m n c) (r m)
                                       ≡⟨ refl ⟩
                                encode m n (decode m n c)
                                       ≡⟨ proof₂ m n c ⟩
                                c
                                ▻

     proof : (m n : ℕ) → (m ≡ n) ≃ code m n
     proof m n = (encode m n) , (qinv-to-isequiv (encode m n) ((decode m n) , ((proof₂ m n) , (proof₁ m n))))

{-
   ua : {A B : Set} → (A ≃ B) → (A ≡ B)
   ua = pr₁ (isequiv-to-qinv idtoeqv axiom-2-10-3)
-}
  -- 2-14

 Assoc : (A : Set) → (m : A → A → A) → Set
 Assoc A m = (x y z : A) → m x (m y z) ≡ m (m x y) z

 SemiGroupStr : (A : Set) → Set
 SemiGroupStr A = ∑ (A → A → A) (Assoc A)

 SemiGroup : Set
 SemiGroup = ∑ Set SemiGroupStr

 module _ {A B : Set} (e : A ≃ B) where

   e₀ : A → B
   e₀ = pr₁ e

   e⁻¹ : B → A
   e⁻¹ = pr₁ (e ⁻¹e) -- (isequiv-to-qinv e₀ (pr₂ e))

   transfer : SemiGroupStr A → SemiGroupStr B
   transfer = transport SemiGroupStr (ua e)

   module _ (s : SemiGroupStr A) where

     m = pr₁ s
     a = pr₂ s

     t = transport SemiGroupStr (ua e) (m , a)

{-
   transport : {A : Set} → (P : A → Set) → {x y : A} → (p : x ≡ y) → P x → P y
   
   transport-id : {A : Set} → (P : A → A) → {x y : A} → (p : x ≡ y) → x → y


    R = λ x → ∑ (P x) (λ u → Q (x , u))

    theorem-2-7-4 :  {A : Set} {P : A → Set} {Q : (∑ A P) → Set} {x y : A} → (p : x ≡ y) → (u : P x) → (z : Q (x , u))
                  → (transport R p) (u , z) ≡ ((p ∗) u , transport Q (2-7-2.pair= (p , refl {P y} {(p ∗) u})) z)
-}

     eq-2-14-2 : transport SemiGroupStr (ua e) (m , a) ≡
                 ( transport {Set} (λ x → (x → x → x)) (ua e) m ,
                   transport {∑ Set (λ x → (x → x → x))} (λ Xm → Assoc (pr₁ Xm) (pr₂ Xm)) (2-7-2.pair= {Set} {λ z → (x x₁ : z) → z} {A , m} {B , transport {Set} (λ x → (x → x → x)) (ua e) m} (ua e , refl)) a
                 )
     eq-2-14-2 = 2-7-4.theorem-2-7-4 {Set} {λ z → (x x₁ : z) → z} {λ Xm → Assoc (pr₁ Xm) (pr₂ Xm)} {A} {B} (ua e) m a

     m' : B → B → B
     m' b₁ b₂ = transport (λ x → x → x → x) (ua e) m b₁ b₂
{-
   A→B = λ x → A x → B x

   theorem-2-9-4 : {x₁ x₂ : X} → (p : x₁ ≡ x₂) → (f : A x₁ → B x₁)
                   → transport A→B p f ≡ λ z → transport B p (f (transport A (p ⁻¹) z))
   ap : {A B : Set} → (f : A → B) → {x y : A} → (x ≡ y) → (f x ≡ f y)

-}

--     my-theorem : {A B : Set} → (e : A ≃ B) → (x : A) → transport id (ua e) ≡ pr₁ e
--     my-theorem e x = transport id (ua e) ≡⟨ {!unicomp!} ⟩
--                      pr₁ e ▻
--   _⁻¹e : {A B : Set} → A ≃ B → B ≃ A
--   uaf⁻1 : {A B : Set} → {f : A ≃ B} → ((ua f) ⁻¹) ≡ (ua (f ⁻¹e))

     transfer-m : (b₁ b₂ : B) → m' b₁ b₂ ≡ e₀ (m (e⁻¹ b₁) (e⁻¹ b₂))
     transfer-m b₁ b₂ =
                m' b₁ b₂
                    ≡⟨ refl ⟩
                transport (λ x → x → x → x) (ua e) m b₁ b₂
                    ≡⟨ ap (λ Q → Q b₁ b₂) {transport (λ x → x → x → x) (ua e) m} (theorem-2-9-4 (ua e) m) ⟩
                (transport (λ x → x → x) (ua e) (m (transport id (ua e ⁻¹) b₁))) b₂
                    ≡⟨ ap (λ Q → Q b₂) (theorem-2-9-4 (ua e) (m (transport id (ua e ⁻¹) b₁))) ⟩
                transport id (ua e) (m (transport id (ua e ⁻¹) b₁) (transport id (ua e ⁻¹) b₂))
                    ≡⟨ ap (λ Q → transport id (ua e) (m (transport id Q b₁) (transport id Q b₂))) (uaf⁻1) ⟩
                transport id (ua e) (m (transport id (ua (e ⁻¹e)) b₁) (transport id (ua (e ⁻¹e)) b₂))
                    ≡⟨ ap₂ (λ Q R → transport id (ua e) (m Q R)) unicomp unicomp ⟩
                transport id (ua e) (m (pr₁ (e ⁻¹e) b₁) (pr₁ (e ⁻¹e) b₂))
                    ≡⟨ unicomp ⟩
                e₀ (m (e⁻¹ b₁) (e⁻¹ b₂))
                ▻

     {-
   theorem-2-7-2 : {A : Set} {P : A → Set} {w w' : ∑ A P}
                   → (w ≡ w') ≃ ∑ (pr₁ w ≡ pr₁ w') (λ p → transport P p (pr₂ w) ≡ pr₂ w')

-}

     equality-of-semigroups : (A : Set) → (m : A → A → A) → (a : Assoc A m)
                            → (B : Set) → (m' : B → B → B) → (a' : Assoc B m')
                            → (_≡_ {∑ Set SemiGroupStr} (A , m , a) (B , m' , a')) ≃
                              ∑ (A ≡ B) (λ p → transport SemiGroupStr p (m , a) ≡ (m' , a'))
     equality-of-semigroups A m a B m' a' = 2-7-2.theorem-2-7-2

 module 2-15 where

   module 2-15-2 {X A B : Set} where

     proj : (X → A × B) → (X → A) × (X → B)
     proj f = (pr₁ ○ f , pr₂ ○ f)

     proj⁻¹ : (X → A) × (X → B) → (X → A × B)
     proj⁻¹ (g , h) x = (g x , h x)

     proof₁ : (f : (X → A) × (X → B)) → proj (proj⁻¹ f) ≡ f
     proof₁ (g , h) = refl

     private temp : (x : A × B) → (pr₁ x , pr₂ x) ≡ x
     temp (u , v) = refl

     proof₂ : (f : X → A × B) → proj⁻¹ (proj f) ≡ f
     proof₂ f = funext (λ x → temp (f x))

     theorem-2-15-2 : isequiv proj
     theorem-2-15-2 = qinv-to-isequiv proj (proj⁻¹ , (proof₁ , proof₂))

   module 2-15-5 {X : Set} {A B : X → Set} where

     proj : ((x : X) → A x × B x) → ((x : X) → A x) × ((x : X) → B x)
     proj f = ((λ x → pr₁ (f x)) , (λ x → pr₂ (f x)))

     proj⁻¹ : ((x : X) → A x) × ((x : X) → B x) → ((x : X) → A x × B x)
     proj⁻¹ (g , h) x = (g x , h x)

     proof₁ : (f : ((x : X) → A x) × ((x : X) → B x)) → proj (proj⁻¹ f) ≡ f
     proof₁ (g , h) = refl

     private temp : {A B : Set} (x : A × B) → (pr₁ x , pr₂ x) ≡ x
     temp (u , v) = refl

     proof₂ : (f : (x : X) → A x × B x) → proj⁻¹ (proj f) ≡ f
     proof₂ f = funext (λ x → temp (f x))

     theorem-2-15-5 : isequiv proj
     theorem-2-15-5 = qinv-to-isequiv proj (proj⁻¹ , (proof₁ , proof₂))

   module 2-15-7 {X : Set} {A : X → Set} {P : (x : X) → A x → Set} where

     -- Axiom of Choice
     proj : ((x : X) → ∑ (A x) (λ a → P x a))
            → ∑ ((x : X) → A x) (λ g → (x : X) → P x (g x))
     proj f = ((λ x → pr₁ (f x)) , (λ x → pr₂ (f x)))

     proj⁻¹ : ∑ ((x : X) → A x) (λ g → (x : X) → P x (g x))
              → ((x : X) → ∑ (A x) (λ a → P x a))
     proj⁻¹ (g , h) x = (g x , h x)

     proof₁ : (f : ∑ ((x : X) → A x) (λ g → (x : X) → P x (g x))) → proj (proj⁻¹ f) ≡ f
     proof₁ (g , h) = refl

     private temp : {A : Set} {B : A → Set} (x : ∑ A B) → (pr₁ x , pr₂ x) ≡ x
     temp (u , v) = refl

     proof₂ : (f : ((x : X) → ∑ (A x) (λ a → P x a))) → proj⁻¹ (proj f) ≡ f
     proof₂ f = funext (λ x → temp (f x))

     theorem-2-15-7 : isequiv proj
     theorem-2-15-7 = qinv-to-isequiv proj (proj⁻¹ , (proof₁ , proof₂))

 module Ex-2-1 where

  _□₁_ : {A : Set} {x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
  _□₁_ refl q = q

  _□₂_ : {A : Set} {x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
  _□₂_ p refl = p

  _□₃_ : {A : Set} {x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
  refl □₃ refl = refl

  ex-2-1-i : {A : Set} {x y z : A} → (p : x ≡ y) → (q : y ≡ z) → (p □₁ q) ≡ (p □₂ q)
  ex-2-1-i refl refl = refl

  ex-2-1-ii : {A : Set} {x y z : A} → (p : x ≡ y) → (q : y ≡ z) → (p □₁ q) ≡ (p □₃ q)
  ex-2-1-ii refl refl = refl

  ex-2-1-iii : {A : Set} {x y z : A} → (p : x ≡ y) → (q : y ≡ z) → (p □₂ q) ≡ (p □₃ q)
  ex-2-1-iii refl refl = refl

 module Ex-2-2 where

  open Ex-2-1

  ex-2-2 : {A : Set} {x y z : A} → (p : x ≡ y) → (q : y ≡ z)
           → ex-2-1-i p q ■ ex-2-1-iii p q ≡ ex-2-1-ii p q
  ex-2-2 refl refl = refl

 module Ex-2-3 where

  open Ex-2-1

  _□₄_ : {A : Set} {x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
  _□₄_ {A} {x} {y} {z} p q = 
         based (λ z q → (x ≡ z))
                p
                z q

  ex-2-1-iv : {A : Set} {x y z : A} → (p : x ≡ y) → (q : y ≡ z) → (p □₁ q) ≡ (p □₄ q)
  ex-2-1-iv refl refl = refl

  ex-2-1-v : {A : Set} {x y z : A} → (p : x ≡ y) → (q : y ≡ z) → (p □₂ q) ≡ (p □₄ q)
  ex-2-1-v refl refl = refl

  ex-2-1-vi : {A : Set} {x y z : A} → (p : x ≡ y) → (q : y ≡ z) → (p □₃ q) ≡ (p □₄ q)
  ex-2-1-vi refl refl = refl

 module Ex-2-4 where

   open import Data.Nat

   -- No idea what 'boundary' means here

   n-dim-path : ℕ → (A : Set) → Set
   n-dim-path 0 A = A
   n-dim-path (suc n) A = ∑ (n-dim-path n A) (λ p → ∑ (n-dim-path n A) (λ q → p ≡ q))

 module Ex-2-5 {A B : Set} {x y z : A} {p : x ≡ y} {f : A → B} where

{-
  transportconst : {A : Set} → {x y : A} → (B : Set) → (p : x ≡ y) → (b : B)
                 → transport (λ x → B) p b ≡ b
  transportconst B refl b = refl
-}

   eq-2-3-6 : f x ≡ f y → (p ∗) (f x) ≡ f y
   eq-2-3-6 q = transportconst B p (f x) ■ q

   eq-2-3-7 : (p ∗) (f x) ≡ f y → f x ≡ f y
   eq-2-3-7 q = (transportconst B p (f x))⁻¹ ■ q

   simple-forward : {A : Set} {x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
   simple-forward p q = p ■ q

   simple-backward : {A : Set} {x y z : A} → (x ≡ y) → (x ≡ z) → (y ≡ z)
   simple-backward p q = p ⁻¹ ■ q

   proof₁ : {A : Set} {x y z : A} → (p : x ≡ y) → (simple-forward {A} {x} {y} {z} p ○ simple-backward p) ~ id
   proof₁ p x = p■p⁻¹■q≡q p x

   proof₂ : {A : Set} {x y z : A} → (p : x ≡ y) → (simple-backward {A} {x} {y} {z} p ○ simple-forward p) ~ id
   proof₂ p x = p⁻¹■p■q≡q p x

   comp-equiv : {A : Set} {x y z : A} → (x ≡ y) → (y ≡ z) ≃ (x ≡ z)
   comp-equiv {A} {x} {y} {z} p = simple-forward p ,
            qinv-to-isequiv (simple-forward {A} {x} {y} {z} p) ((simple-backward p) , proof₁ p , proof₂ p)


   ex-2-5 : (f x ≡ f y) ≃ ((p ∗) (f x) ≡ f y)
   ex-2-5 = comp-equiv (transportconst B p (f x))

 module Ex-2-6 where
   
   simple-forward : {A : Set} {x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
   simple-forward p q = p ■ q

   simple-backward : {A : Set} {x y z : A} → (x ≡ y) → (x ≡ z) → (y ≡ z)
   simple-backward p q = p ⁻¹ ■ q

   proof₁ : {A : Set} {x y z : A} → (p : x ≡ y) → (simple-forward {A} {x} {y} {z} p ○ simple-backward p) ~ id
   proof₁ p x = p■p⁻¹■q≡q p x

   proof₂ : {A : Set} {x y z : A} → (p : x ≡ y) → (simple-backward {A} {x} {y} {z} p ○ simple-forward p) ~ id
   proof₂ p x = p⁻¹■p■q≡q p x

   comp-equiv : {A : Set} {x y z : A} → (x ≡ y) → (y ≡ z) ≃ (x ≡ z)
   comp-equiv {A} {x} {y} {z} p = simple-forward p ,
            qinv-to-isequiv (simple-forward {A} {x} {y} {z} p) ((simple-backward p) , proof₁ p , proof₂ p)

 module Ex-2-7 {A A' : Set} {B : A → Set} {B' : A' → Set} where

  f : (g : A → A') → (h : ((x : A) → B x → B' (g x))) → ∑ A B → ∑ A' B'
  f g h x = (g (pr₁ x), h (pr₁ x) (pr₂ x))

{-
  lemma-2-3-11 : {A : Set} → (P Q : A → Set) → {x y : A} → (f : (x : A) → P x → Q x) → (p : x ≡ y) → (u : P x) → transport Q p (f x u) ≡ f y (transport P p u)


   pair= : {w w' : ∑ A P} → ∑ (pr₁ w ≡ pr₁ w') (λ p → (p ∗)(pr₂ w) ≡ pr₂ w') → (w ≡ w')

   ap : {A B : Set} → (f : A → B) → {x y : A} → (x ≡ y) → (f x ≡ f y)

  lemma-2-3-10 : {A B : Set} → (f : A → B) → (P : B → Set) → {x y : A} → (p : x ≡ y) → (u : P (f x))
                             → transport (P ○ f) p u ≡ transport P (ap f p) u

-}

{-
  temp₁ : {x y : ∑ A B} → (g : A → A') → (h : ((x : A) → B x → B' (g x)))
         → (p : pr₁ x ≡ pr₁ y) (q : transport B p (pr₂ x) ≡ pr₂ y)
         → x ≡ y
  temp₁ g h p q = (2-7-2.pair= (p , q))

  temp₂ : {x y : ∑ A B} → (g : A → A') → (h : ((x : A) → B x → B' (g x)))
         → (p : pr₁ x ≡ pr₁ y) (q : transport B p (pr₂ x) ≡ pr₂ y)
         → f g h x ≡ f g h y
  temp₂ {x} {y} g h p q = ap {∑ A B} {∑ A' B'} (f g h) {x} {y} (2-7-2.pair= (p , q))

  temp₃ : {x y : ∑ A B} → (g : A → A') → (h : ((x : A) → B x → B' (g x)))
         → (p : pr₁ x ≡ pr₁ y) (q : transport B p (pr₂ x) ≡ pr₂ y)
         → transport (B' ○ g) p (h (pr₁ x) (pr₂ x)) ≡ h (pr₁ y) (transport B p (pr₂ x))
  temp₃ {x} {y} g h p q = 
                 lemma-2-3-11 {A} B (B' ○ g) h p (pr₂ x)

  temp₄ : {x y : ∑ A B} → (g : A → A') → (h : ((x : A) → B x → B' (g x)))
         → (p : pr₁ x ≡ pr₁ y) (q : transport B p (pr₂ x) ≡ pr₂ y)
         → h (pr₁ y) ((transport B p) (pr₂ x)) ≡ h (pr₁ y) (pr₂ y)
  temp₄ {x} {y} g h p q = ap (h (pr₁ y)) q

  temp₅ : {x y : ∑ A B} → (g : A → A') → (h : ((x : A) → B x → B' (g x)))
         → (p : pr₁ x ≡ pr₁ y) (q : transport B p (pr₂ x) ≡ pr₂ y)
         → transport (B' ○ g) p (h (pr₁ x) (pr₂ x)) ≡ h (pr₁ y) (pr₂ y)
  temp₅ {x} {y} g h p q = lemma-2-3-11 {A} B (B' ○ g) h p (pr₂ x) ■ ap (h (pr₁ y)) q

  temp₆ : {x y : ∑ A B} → (g : A → A') → (h : ((x : A) → B x → B' (g x)))
         → (p : pr₁ x ≡ pr₁ y) (q : transport B p (pr₂ x) ≡ pr₂ y)
         → transport (B' ○ g) p (h (pr₁ x) (pr₂ x)) ≡ transport B' (ap g p) (h (pr₁ x) (pr₂ x))
  temp₆ {x} {y} g h p q = lemma-2-3-10 g B' p (h (pr₁ x) (pr₂ x))

  temp₇ : {x y : ∑ A B} → (g : A → A') → (h : ((x : A) → B x → B' (g x)))
         → (p : pr₁ x ≡ pr₁ y) (q : transport B p (pr₂ x) ≡ pr₂ y)
         → transport B' (ap g p) (h (pr₁ x) (pr₂ x)) ≡ h (pr₁ y) (pr₂ y)
  temp₇ {x} {y} g h p q = lemma-2-3-10 g B' p (h (pr₁ x) (pr₂ x)) ⁻¹ ■ lemma-2-3-11 {A} B (B' ○ g) h p (pr₂ x) ■ ap (h (pr₁ y)) q

  temp₈ : {x y : ∑ A B} → (g : A → A') → (h : ((x : A) → B x → B' (g x)))
         → (p : pr₁ x ≡ pr₁ y) (q : transport B p (pr₂ x) ≡ pr₂ y)
         → f g h x ≡ f g h y
  temp₈ {x} {y} g h p q = 2-7-2.pair= (
                 ap g p ,
                 lemma-2-3-10 g B' p (h (pr₁ x) (pr₂ x)) ⁻¹ ■ lemma-2-3-11 {A} B (B' ○ g) h p (pr₂ x) ■ ap (h (pr₁ y)) q)    
-}

  ex-2-7 : {x y : ∑ A B} → (g : A → A') → (h : ((x : A) → B x → B' (g x)))
         → (p : pr₁ x ≡ pr₁ y) (q : transport B p (pr₂ x) ≡ pr₂ y)
         → ap {∑ A B} {∑ A' B'} (f g h) {x} {y} (2-7-2.pair= (p , q)) ≡ 2-7-2.pair= (
                 ap g p ,
                 lemma-2-3-10 g B' p (h (pr₁ x) (pr₂ x)) ⁻¹ ■ lemma-2-3-11 {A} B (B' ○ g) h p (pr₂ x) ■ ap (h (pr₁ y)) q)
  ex-2-7 {a , b} {.a , .b} g h refl refl = refl

 module Ex-2-8 {A A' B B' : Set} where

  f : (g : A → A') → (h : B → B') → A + B → A' + B'
  f g h (inl x) = inl (g x)
  f g h (inr x) = inr (h x)

  a-path-in : Set → Set
  a-path-in A = ∑ A (λ x → ∑ A (λ y → x ≡ y))

  temp₃ : (g : A → A') → (h : B → B') → (a-path-in A + a-path-in B) → a-path-in (A' + B')
  temp₃ g h (inl (a , a' , p)) = inl (g a) , inl (g a') , ap inl (ap g p)
  temp₃ g h (inr (b , b' , q)) = inr (h b) , inr (h b') , ap inr (ap h q)

  temp₄ : (g : A → A') → (h : B → B') → (a-path-in A + a-path-in B) → a-path-in (A' + B')
  temp₄ g h (inl (a , a' , p)) = inl (g a) , inl (g a') , ap (f g h) (ap inl p)
  temp₄ g h (inr (b , b' , q)) = inr (h b) , inr (h b') , ap (f g h) (ap inr q)

  ex-2-8 : (g : A → A') → (h : B → B') → (p : a-path-in A + a-path-in B)
           → temp₃ g h p ≡ temp₄ g h p
  ex-2-8 g h (inl (a , .a , refl)) = refl
  ex-2-8 g h (inr (b , .b , refl)) = refl

 module Ex-2-9-i {A B X : Set} where

   f : (A + B → X) → ((A → X) × (B → X))
   f g = (λ x → g (inl x)) , (λ x → g (inr x))

   f⁻¹ : ((A → X) × (B → X)) → (A + B → X)
   f⁻¹ (g , h) (inl x) = g x
   f⁻¹ (g , h) (inr x) = h x

   forward : (x : (A → X) × (B → X)) → f (f⁻¹ x) ≡ x
   forward (g , h) = refl

   backward-0 : (g : A + B → X) → (x : A + B) → f⁻¹ ((λ x₁ → g (inl x₁)) , (λ x₁ → g (inr x₁))) x ≡ g x
   backward-0 g (inl x) = refl
   backward-0 g (inr x) = refl

   backward : (g : A + B → X) → f⁻¹ (f g) ≡ g
   backward g = funext (backward-0 g)

   ex-2-9-i : (A + B → X) ≃ ((A → X) × (B → X))
   ex-2-9-i = f , (qinv-to-isequiv f (f⁻¹ , (forward , backward)))

 module Ex-2-9-ii {A B : Set} {X : (A + B) → Set} where

   f : ((u : A + B) → X u) → ((x : A) → X (inl x)) × ((y : B) → X (inr y))
   f g = (λ x → g (inl x)) , (λ x → g (inr x))

   f⁻¹ : ((x : A) → X (inl x)) × ((y : B) → X (inr y)) → ((u : A + B) → X u)
   f⁻¹ (g , h) (inl x) = g x
   f⁻¹ (g , h) (inr x) = h x

   forward : (x : ((u : A) → X (inl u)) × ((v : B) → X (inr v))) → f (f⁻¹ x) ≡ x
   forward (g , h) = refl

   backward-0 : (g : ((u : A + B) → X u)) → (x : A + B) → f⁻¹ ((λ x₁ → g (inl x₁)) , (λ x₁ → g (inr x₁))) x ≡ g x
   backward-0 g (inl x) = refl
   backward-0 g (inr x) = refl

   backward : (g : ((u : A + B) → X u)) → f⁻¹ (f g) ≡ g
   backward g = funext (backward-0 g)

   ex-2-9-ii : ((u : A + B) → X u) ≃ (((x : A) → X (inl x)) × ((y : B) → X (inr y)))
   ex-2-9-ii = f , (qinv-to-isequiv f (f⁻¹ , (forward , backward)))

 module Ex-2-10 {A : Set} {B : A → Set} {C : ∑ A B → Set} where
 
   f : ∑ A (λ x → ∑ (B x) (λ y → C (x , y))) → ∑ (∑ A B) C
   f (a , b , c) = (a , b) , c

   f⁻¹ : ∑ (∑ A B) C → ∑ A (λ x → ∑ (B x) (λ y → C (x , y))) 
   f⁻¹ ((a , b) , c) = a , b , c

   forward : (x : ∑ (∑ A B) C) → f (f⁻¹ x) ≡ x
   forward ((_ , _) , _) = refl

   backward : (x : ∑ A (λ x → ∑ (B x) (λ y → C (x , y)))) → f⁻¹ (f x) ≡ x
   backward (_ , _ , _) = refl

   ex-2-10 : ∑ A (λ x → ∑ (B x) (λ y → C (x , y))) ≃ ∑ (∑ A B) C
   ex-2-10 = f , (qinv-to-isequiv f (f⁻¹ , (forward , backward)))

 module Ex-2-11 {A B C : Set} {f : A → C} {g : B → C} where

   pullback : {A B C : Set} → (f : A → C) → (g : B → C) → Set
   pullback {A} {B} {C} f g = ∑ A (λ a → ∑ B (λ b → f a ≡ g b))

   P = pullback {A} {B} {C} f g

   is-pullback-square : (P : Set) → Set
   is-pullback-square P = (X : Set) → (X → P) ≃ pullback {X → A} {X → B} {X → C} (_○_ f) (_○_ g)

   forward : (X : Set) → (X → P) → pullback {X → A} {X → B} {X → C} (_○_ f) (_○_ g)
   forward X p = (λ x → {!!}) , ((λ x → {!!}) , {!!})

   ex-2-11 : is-pullback-square P
   ex-2-11 = {!!}
