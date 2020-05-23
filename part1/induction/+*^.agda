module +*^ where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_)

open import Induction′ using (+-identityʳ)
open import *-comm using (*-comm)
open import *-assoc using (*-assoc)

-- 積法の左単位元
*-identityˡ : ∀ (n : ℕ) → 1 * n ≡ n
*-identityˡ zero    = refl
*-identityˡ (suc n) =
  begin
    1 * (suc n)
  ≡⟨⟩
    (suc n) + (zero * (suc n))
  ≡⟨⟩
    (suc n) + zero
  ≡⟨ +-identityʳ (suc n) ⟩
    (suc n)
  ∎

*-swap : ∀ (m n p : ℕ) → m * n * p ≡ m * p * n
*-swap m n p =
  begin
    (m * n) * p
  ≡⟨ *-assoc m n p ⟩
    m * (n * p)
  ≡⟨ cong (m *_) (*-comm n p) ⟩
    m * (p * n)
  ≡⟨ sym (*-assoc m p n) ⟩
    (m * p) * n
  ∎

^-distribˡ-+-* : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-distribˡ-+-* m zero p =
  begin
    m ^ (zero + p)
  ≡⟨⟩
    m ^ p
  ≡⟨ sym (*-identityˡ (m ^ p)) ⟩
    1 * (m ^ p)
  ≡⟨⟩
    (m ^ zero) * (m ^ p)
  ∎
^-distribˡ-+-* zero (suc n) p =
  begin
    zero ^ ((suc n) + p)
  ≡⟨⟩
    zero * (zero ^ (n + p))
  ≡⟨⟩
    zero
  ≡⟨⟩
    (zero ^ (suc n)) * (zero ^ p)
  ∎
^-distribˡ-+-* (suc m) (suc n) p =
  begin
    (suc m) ^ ((suc n) + p)
  ≡⟨⟩
    (suc m) * ((suc m) ^ (n + p))
  ≡⟨ cong ((suc m) *_) (^-distribˡ-+-* ((suc m)) n p) ⟩
    (suc m) * (((suc m) ^ n) * ((suc m) ^ p))
  ≡⟨ sym (*-assoc (suc m) (suc m ^ n) (suc m ^ p)) ⟩
    ((suc m) * ((suc m) ^ n)) * ((suc m) ^ p)
  ≡⟨⟩
    ((suc m) ^ (suc n)) * ((suc m) ^ p)
  ∎

^-distribʳ-* : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^-distribʳ-* m n zero =
  begin
    (m * n) ^ zero
  ≡⟨⟩
    1
  ≡⟨⟩
    (m ^ zero) * (n ^ zero)
  ∎
^-distribʳ-* m n (suc p) =
  begin
    (m * n) ^ (suc p)
  ≡⟨⟩
    (m * n) * ((m * n) ^ p)
  ≡⟨ cong ((m * n) *_) (^-distribʳ-* m n p) ⟩
    (m * n) * ((m ^ p) * (n ^ p))
  ≡⟨ sym (*-assoc (m * n) (m ^ p) (n ^ p)) ⟩
    ((m * n) * (m ^ p)) * (n ^ p)
  ≡⟨ cong (_* (n ^ p)) (*-swap m n (m ^ p)) ⟩
    ((m * (m ^ p)) * n) * (n ^ p)
  ≡⟨⟩
    ((m ^ (suc p)) * n) * (n ^ p)
  ≡⟨ *-assoc (m * (m ^ p)) n (n ^ p) ⟩
    (m ^ (suc p)) * (n * (n ^ p))
  ≡⟨⟩
    (m ^ (suc p)) * (n ^ (suc p))
  ∎

^-*-assoc : ∀ (m n p : ℕ) → (m ^ n) ^ p ≡ m ^ (n * p)
^-*-assoc m n zero =
  begin
    (m ^ n) ^ zero
  ≡⟨⟩
    1
  ≡⟨⟩
    m ^ (zero * n)
  ≡⟨ cong (m ^_) (*-comm zero n) ⟩
    m ^ (n * zero)
  ∎
^-*-assoc m n (suc p) =
  begin
    (m ^ n) ^ (suc p)
  ≡⟨⟩
    (m ^ n) * ((m ^ n) ^ p)
  ≡⟨ cong ((m ^ n) *_) (^-*-assoc m n p) ⟩
    (m ^ n) * (m ^ (n * p))
  ≡⟨ sym (^-distribˡ-+-* m n (n * p)) ⟩
    m ^ (n + (n * p))
  ≡⟨ cong (λ p*n → m ^ (n + p*n)) (*-comm n p) ⟩
    m ^ (n + (p * n))
  ≡⟨⟩
    m ^ ((suc p) * n)
  ≡⟨ cong (m ^_) (*-comm (suc p) n) ⟩
    m ^ (n * (suc p))
  ∎
