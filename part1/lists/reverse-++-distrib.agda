module reverse-++-distrib where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong)
open Eq.≡-Reasoning
open import lists using (List; []; _∷_; [_]; _++_; ++-assoc; ++-identityʳ; reverse)

-- 結合したリストの逆順は、逆順にしたリストの逆順の結合と等しいことの証明
reverse-++-distrib : ∀ {A : Set} → (xs ys : List A)
  → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-distrib [] ys =
  begin
    reverse ([] ++ ys)
  ≡⟨⟩
    reverse ys
  ≡⟨ sym (++-identityʳ (reverse ys)) ⟩
    reverse ys ++ []
  ≡⟨⟩
    reverse ys ++ reverse []
  ∎
reverse-++-distrib (x ∷ xs) ys =
  begin
    reverse (x ∷ xs ++ ys)
  ≡⟨⟩
    reverse (xs ++ ys) ++ [ x ]
  ≡⟨ cong (_++ [ x ]) (reverse-++-distrib xs ys) ⟩
    (reverse ys ++ reverse xs) ++ [ x ]
  ≡⟨ ++-assoc (reverse ys) (reverse xs) [ x ] ⟩
    reverse ys ++ (reverse xs ++ [ x ])
  ≡⟨⟩
    reverse ys ++ reverse (x ∷ xs)
  ∎
