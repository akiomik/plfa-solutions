module reverse-involution where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong)
open Eq.≡-Reasoning
open import lists using (List; []; _∷_; [_]; _++_; reverse)
open import reverse-++-distrib using (reverse-++-distrib)

-- reverseが対合(involution)である事の証明
reverse-involution : {A : Set} → (xs : List A)
  → reverse (reverse xs) ≡ xs
reverse-involution [] =
  begin
    reverse (reverse [])
  ≡⟨⟩
    reverse []
  ≡⟨⟩
    []
  ∎
reverse-involution (x ∷ xs) =
  begin
    reverse (reverse (x ∷ xs))
  ≡⟨⟩
    reverse ((reverse xs) ++ [ x ])
  ≡⟨ reverse-++-distrib (reverse xs) [ x ] ⟩
    (reverse [ x ]) ++ (reverse (reverse xs))
  ≡⟨⟩
    [ x ] ++ reverse (reverse xs)
  ≡⟨ cong (x ∷_) (reverse-involution xs) ⟩
    x ∷ xs
  ∎
