module ≤-Reasoning where

open import Equality using (_≡_; refl; ℕ; zero; suc; _+_; +-comm)

data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {n : ℕ}
      --------
    → zero ≤ n

  s≤s : ∀ {m n : ℕ}
    → m ≤ n
      -------------
    → suc m ≤ suc n

infix 4 _≤_

≤-refl : ∀ {n : ℕ}
    -----
  → n ≤ n
≤-refl {zero}  = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀ {m n p : ℕ}
  → m ≤ n
  → n ≤ p
    -----
  → m ≤ p
≤-trans z≤n       _         = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

module ≤-Reasoning where
  infix  1 begin_
  infixr 2 _≤⟨⟩_ _≤⟨_⟩_ _≡⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {m n : ℕ}
    → m ≤ n
      -----
    → m ≤ n
  begin m≤n = m≤n

  _≤⟨⟩_ : ∀ (m : ℕ) {n : ℕ}
    → m ≤ n
      -----
    → m ≤ n
  m ≤⟨⟩ m≤n = m≤n

  _≤⟨_⟩_ : ∀ (m : ℕ) {n p : ℕ}
    → m ≤ n
    → n ≤ p
      -----
    → m ≤ p
  m ≤⟨ m≤n ⟩ n≤p = ≤-trans m≤n n≤p

  _≡⟨_⟩_ : ∀ (m : ℕ) {n p : ℕ}
    → m ≡ n
    → n ≤ p
      -----
    → m ≤ p
  m ≡⟨ refl ⟩ n≤p = n≤p

  _∎ : ∀ (n : ℕ)
      -----
    → n ≤ n
  n ∎ = ≤-refl

open ≤-Reasoning

-- +-monoʳ-≤ : ∀ (n p q : ℕ)
--   → p ≤ q
--     -------------
--   → n + p ≤ n + q
-- +-monoʳ-≤ zero    p q p≤q = p≤q
-- +-monoʳ-≤ (suc n) p q p≤q = s≤s (+-monoʳ-≤ n p q p≤q)

+-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    -------------
  → n + p ≤ n + q
+-monoʳ-≤ zero p q p≤q =
  begin
    zero + p
  ≤⟨ p≤q ⟩
    zero + q
  ∎
+-monoʳ-≤ (suc n) p q p≤q =
  begin
    (suc n) + p
  ≤⟨ s≤s (+-monoʳ-≤ n p q p≤q) ⟩
    (suc n) + q
  ∎

-- +-monoˡ-≤ : ∀ (m n p : ℕ)
--   → m ≤ n
--     -------------
--   → m + p ≤ n + p
-- +-monoˡ-≤ m n p m≤n  rewrite +-comm m p | +-comm n p = +-monoʳ-≤ p m n m≤n

+-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n =
  begin
    m + p
  ≡⟨ +-comm m p ⟩
    p + m
  ≤⟨ +-monoʳ-≤ p m n m≤n ⟩
    p + n
  ≡⟨ +-comm p n ⟩
    n + p
  ∎

-- +-mono-≤ : ∀ (m n p q : ℕ)
--   → m ≤ n
--   → p ≤ q
--     -------------
--   → m + p ≤ n + q
-- +-mono-≤ m n p q m≤n p≤q = ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)

+-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    -------------
  → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q =
  begin
    m + p
  ≤⟨ +-monoˡ-≤ m n p m≤n ⟩
    n + p
  ≤⟨ +-monoʳ-≤ n p q p≤q ⟩
    n + q
  ∎
