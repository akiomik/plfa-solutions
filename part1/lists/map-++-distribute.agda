module map-++-distribute where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning
open import lists using (List; []; _∷_; _++_; map)

-- リストの結合に関するmapの分配法則の証明
map-++-distribute : {A B : Set} → (f : A → B) → (xs ys : List A)
  → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-distribute f [] ys =
  begin
    map f ([] ++ ys)
  ≡⟨⟩
    map f ys
  ≡⟨⟩
    map f [] ++ map f ys
  ∎
map-++-distribute f (x ∷ xs) ys =
  begin
    map f ((x ∷ xs) ++ ys)
  ≡⟨⟩
    f x ∷ map f (xs ++ ys)
  ≡⟨ cong (f x ∷_) (map-++-distribute f xs ys) ⟩
    f x ∷ map f xs ++ map f ys
  ≡⟨⟩
    map f (x ∷ xs) ++ map f ys
  ∎
