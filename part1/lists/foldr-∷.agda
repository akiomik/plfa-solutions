module foldr-∷ where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; sym; cong)
open Eq.≡-Reasoning
open import lists using (List; _∷_; []; _++_; foldr)
open import foldr-++ using (foldr-++)

-- 畳み込みの除去則
foldr-∷ : ∀ {A : Set} → (xs : List A)
  → foldr _∷_ [] xs ≡ xs
foldr-∷ [] =
  begin
    foldr _∷_ [] []
  ≡⟨⟩
    []
  ∎
foldr-∷ (x ∷ xs) =
  begin
    foldr _∷_ [] (x ∷ xs)
  ≡⟨⟩
    x ∷ (foldr _∷_ [] xs)
  ≡⟨ cong (x ∷_) (foldr-∷ xs) ⟩
    x ∷ xs
  ∎

-- リストの結合が畳み込みで表現できることの証明
++-foldr-∷ : ∀ {A : Set} → (xs ys : List A)
  → xs ++ ys ≡ foldr _∷_ ys xs
++-foldr-∷ [] ys =
  begin
    [] ++ ys
  ≡⟨⟩
    ys
  ≡⟨⟩
    foldr _∷_ ys []
  ∎
++-foldr-∷ (x ∷ xs) ys =
  begin
    (x ∷ xs) ++ ys
  ≡⟨⟩
    x ∷ (xs ++ ys)
  ≡⟨ cong (x ∷_) (++-foldr-∷ xs ys) ⟩
    x ∷ (foldr _∷_ ys xs)
  ≡⟨⟩
    foldr _∷_ ys (x ∷ xs)
  ∎

-- ++-foldr-∷の別証明 (foldr-++版)
++-foldr-∷′ : ∀ {A : Set} → (xs ys : List A)
  → xs ++ ys ≡ foldr _∷_ ys xs
++-foldr-∷′ xs ys =
  begin
    xs ++ ys
  ≡⟨ sym (foldr-∷ (xs ++ ys)) ⟩
    foldr _∷_ [] (xs ++ ys)
  ≡⟨ foldr-++ _∷_ [] xs ys ⟩
    foldr _∷_ (foldr _∷_ [] ys) xs
  ≡⟨ cong (λ ys′ → foldr _∷_ ys′ xs) (foldr-∷ ys) ⟩
    foldr _∷_ ys xs
  ∎
