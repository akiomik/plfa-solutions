module map-is-foldr where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; cong)
open Eq.≡-Reasoning
open import lists using (List; []; _∷_; map; foldr)

postulate
  -- 外延性の公理
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

-- 外延性の公理を利用した証明のための補題
lemma : ∀ {A B : Set} → (f : A → B) → (xs : List A)
  → map f xs ≡ foldr (λ x xs → f x ∷ xs) [] xs
lemma f [] =
  begin
    map f []
  ≡⟨⟩
    []
  ≡⟨⟩
    foldr (λ x xs → f x ∷ xs) [] []
  ∎
lemma f (x ∷ xs) =
  begin
    map f (x ∷ xs)
  ≡⟨⟩
    f x ∷ map f xs
  ≡⟨ cong (f x ∷_) (lemma f xs) ⟩
    f x ∷ foldr (λ x xs → f x ∷ xs) [] xs
  ≡⟨⟩
    foldr (λ x xs → f x ∷ xs) [] (x ∷ xs)
  ∎

-- mapが畳み込みで表現できることの証明
map-is-foldr : ∀ {A B : Set} → (f : A → B)
  → map f ≡ foldr (λ x xs → f x ∷ xs) []
map-is-foldr f = extensionality (lemma f)
