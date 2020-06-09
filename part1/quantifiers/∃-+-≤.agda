module ∃-+-≤ where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-suc)

open import Quantifiers using (⟨_,_⟩; ∃-syntax)

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ}
      --------
    → zero ≤ n

  s≤s : ∀ {m n : ℕ}
    → m ≤ n
      -------------
    → suc m ≤ suc n

-- 任意の自然数y, zについて、x + y = z を満たすある自然数xが存在するとき、y ≤ z
∃-+-≤ : ∀ {y z : ℕ}
  → ∃[ x ] (x + y ≡ z)
    ------------------
  → y ≤ z
∃-+-≤ {zero}  (⟨ zero , refl ⟩)  = z≤n
∃-+-≤ {suc y} (⟨ zero , refl ⟩)  = s≤s (∃-+-≤ {y} ⟨ zero , refl ⟩)
∃-+-≤ {zero}  (⟨ suc x , refl ⟩) = z≤n
∃-+-≤ {suc y} (⟨ suc x , refl ⟩) = s≤s (∃-+-≤ {y} ⟨ suc x , sym (+-suc x y) ⟩)
