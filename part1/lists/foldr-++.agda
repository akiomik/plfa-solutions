module foldr-++ where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; cong)
open Eq.≡-Reasoning
open import lists using (List; _∷_; []; _++_; foldr)
 
-- 結合したリストの重畳は、重畳した結果を初期値とした重畳と等しいことの証明
foldr-++ : ∀ {A B : Set} → (_⊗_ : A → B → B) → (e : B) → (xs ys : List A)
  → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs
foldr-++ _⊗_ e [] ys =
  begin
    foldr _⊗_ e ([] ++ ys)
  ≡⟨⟩
    foldr _⊗_ e ys
  ≡⟨⟩
    foldr _⊗_ (foldr _⊗_ e ys) []
  ∎
foldr-++ _⊗_ e (x ∷ xs) ys =
  begin
    foldr _⊗_ e ((x ∷ xs) ++ ys)
  ≡⟨⟩
    x ⊗ (foldr _⊗_ e (xs ++ ys))
  ≡⟨ cong (x ⊗_) (foldr-++ _⊗_ e xs ys) ⟩
    x ⊗ (foldr _⊗_ (foldr _⊗_ e ys) xs)
  ≡⟨⟩
    foldr _⊗_ (foldr _⊗_ e ys) (x ∷ xs)
  ∎
