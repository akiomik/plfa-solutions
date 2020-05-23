module ∸-+-assoc where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

open import Induction′ using (+-assoc; +-comm)

∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc m zero p =
  begin
    m ∸ zero ∸ p
  ≡⟨⟩
    m ∸ p
  ≡⟨⟩
    m ∸ (zero + p)
  ∎
∸-+-assoc m n zero =
  begin
    m ∸ n ∸ zero
  ≡⟨⟩
    m ∸ n
  ≡⟨⟩
    m ∸ (zero + n) 
  ≡⟨ cong (m ∸_) (+-comm zero n) ⟩
    m ∸ (n + zero)
  ∎
∸-+-assoc zero (suc n) (suc p) =
  begin
    zero ∸ (suc n) ∸ (suc p)
  ≡⟨⟩
    zero ∸ (suc p)
  ≡⟨⟩
    zero
  ≡⟨⟩
    zero ∸ ((suc n) + (suc p))
  ∎
∸-+-assoc (suc m) (suc n) p =
  begin
    (suc m) ∸ (suc n) ∸ p
  ≡⟨⟩
    m ∸ n ∸ p
  ≡⟨ ∸-+-assoc m n p ⟩
    m ∸ (n + p)
  ≡⟨⟩
    (suc m) ∸ ((suc n) + p)
  ∎
