module foldl where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning

open import lists using (List; []; _∷_; [_,_,_])

foldl : ∀ {A B : Set} → (B → A → B) → B → List A → B
foldl _⊗_ e []       = e
foldl _⊗_ e (x ∷ xs) = foldl _⊗_ (e ⊗ x) xs

test-foldl : ∀ {A B : Set} → (_⊗_ : B → A → B) → (e : B) → (x y z : A)
  → foldl _⊗_ e [ x , y , z ] ≡ ((e ⊗ x) ⊗ y) ⊗ z
test-foldl _⊗_ e x y z = refl
