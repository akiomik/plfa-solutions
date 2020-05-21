import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

open import Naturals using (_∸_)

module ∸-example where

∸-example₁ : 5 ∸ 3 ≡ 2
∸-example₁ =
  begin
    5 ∸ 3
  ≡⟨⟩
    4 ∸ 2
  ≡⟨⟩
    3 ∸ 1
  ≡⟨⟩
    2 ∸ 0
  ≡⟨⟩
    2
  ∎

∸-example₂ : 3 ∸ 5 ≡ 0
∸-example₂ =
  begin
    3 ∸ 5
  ≡⟨⟩
    2 ∸ 4
  ≡⟨⟩
    1 ∸ 3
  ≡⟨⟩
    0 ∸ 2
  ≡⟨⟩
    0
  ∎
