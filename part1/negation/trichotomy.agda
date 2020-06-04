module trichotomy where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)

open import Negation using (¬_; _≢_)

infix 4 _<_
data _<_ : ℕ → ℕ → Set where
  z<s : ∀ {n : ℕ}
      ------------
    → zero < suc n

  s<s : ∀ {m n : ℕ}
    → m < n
      -------------
    → suc m < suc n

infix 4 _≮_
_≮_ : ∀ (m n : ℕ) → Set
m ≮ n = ¬ (m < n)

-- 1 + m ≡ 1 + n ならば m ≡ n
sm≡sn→m≡n : ∀ {m n : ℕ} → suc m ≡ suc n → m ≡ n
sm≡sn→m≡n refl = refl

-- m ≢ n ならば 1 + m ≢ 1 + n
m≢n→sm≢sn : ∀ {m n : ℕ} → m ≢ n → suc m ≢ suc n
m≢n→sm≢sn m≢n = λ{ sm≡sn → m≢n (sm≡sn→m≡n sm≡sn) }

-- m ≮ n ならば 1 + m ≮ 1 + n
m≮n→sm≮sn : ∀ {m n : ℕ} → m ≮ n → suc m ≮ suc n
m≮n→sm≮sn m≮n = λ{ (s<s m<n) → m≮n m<n }

-- 三分律の証明
trichotomy : ∀ (m n : ℕ)
  → (m < n × m ≢ n × n ≮ m)
  ⊎ (m ≮ n × m ≡ n × n ≮ m)
  ⊎ (m ≮ n × m ≢ n × n < m)
trichotomy zero    zero                                              = inj₂ (inj₁ ⟨ (λ()) , ⟨ refl , (λ()) ⟩ ⟩)
trichotomy zero    (suc n)                                           = inj₁ ⟨ z<s , ⟨ (λ()) , (λ()) ⟩ ⟩
trichotomy (suc m) zero                                              = inj₂ (inj₂ ⟨ (λ()) , ⟨ (λ()) , z<s ⟩ ⟩)
trichotomy (suc m) (suc n) with trichotomy m n
...                           | inj₁ ⟨ m<n , ⟨ m≢n , n≮m ⟩ ⟩         = inj₁ ⟨ s<s m<n , ⟨ m≢n→sm≢sn m≢n , m≮n→sm≮sn n≮m ⟩ ⟩
...                           | inj₂ (inj₁ ⟨ m≮n , ⟨ refl , n≮m ⟩ ⟩) = inj₂ (inj₁ ⟨ m≮n→sm≮sn m≮n , ⟨ refl , m≮n→sm≮sn n≮m ⟩ ⟩)
...                           | inj₂ (inj₂ ⟨ m≮n , ⟨ m≢n , n<m ⟩ ⟩)  = inj₂ (inj₂ ⟨ m≮n→sm≮sn m≮n , ⟨ m≢n→sm≢sn m≢n , s<s n<m ⟩ ⟩)
