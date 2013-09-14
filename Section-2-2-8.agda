{-# OPTIONS --without-K --type-in-type #-}

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

module Section-2-2-8 where

  data unit : Set where
    ⋆ : unit

  private f : (x y : unit) → (x ≡ y) → unit
  f x y _ = ⋆

  private g : (x y : unit) → unit → (x ≡ y)
  g ⋆ ⋆ ⋆ = refl

  private fg≡id : (x y : unit) → (r : unit) → f x y (g x y r) ≡ r
  fg≡id x y ⋆ = refl

  ind⋆ : (C : unit → Set) → (x : unit) → C ⋆ → C x
  ind⋆ _ ⋆ z = z

  private gf≡id : (x y : unit) → (r : x ≡ y) → g x y (f x y r) ≡ r
  gf≡id x .x refl = ind⋆ (λ x → g x x (f x x refl) ≡ refl) x refl

  theorem-2-8-1 : (x y : unit) → (x ≡ y) ≃ unit
  theorem-2-8-1 x y = (f x y , qinv-to-isequiv (λ _ → ⋆) (g x y , (fg≡id x y , gf≡id x y)))
