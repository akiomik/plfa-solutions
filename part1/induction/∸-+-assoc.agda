module ∸-+-assoc where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)

open import Induction′ using (+-comm)
open import 0∸n≡0 using (0∸n≡0)

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
∸-+-assoc zero n p =
  begin
    zero ∸ n ∸ p
  ≡⟨ cong (_∸ p) (0∸n≡0 n) ⟩
    zero ∸ p
  ≡⟨ 0∸n≡0 p ⟩
    zero
  ≡⟨ sym (0∸n≡0 (n + p)) ⟩
    zero ∸ (n + p)
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
