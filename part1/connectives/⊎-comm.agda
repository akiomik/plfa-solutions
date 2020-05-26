module ⊎-comm where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Connectives using (_≃_; _⊎_; inj₁; inj₂)

-- 要素の交換
⊎-swap : ∀ {A B : Set} → A ⊎ B → B ⊎ A
⊎-swap (inj₁ a) = inj₂ a
⊎-swap (inj₂ b) = inj₁ b

-- 「交換の交換」が恒等射であることの証明
⊎-swap-elim : ∀ {A B : Set} → (w : A ⊎ B)
  → ⊎-swap (⊎-swap w) ≡ w
⊎-swap-elim (inj₁ a) = refl
⊎-swap-elim (inj₂ b) = refl

-- 直和の可換性が同型であることの証明
⊎-comm : ∀ {A B : Set} → A ⊎ B ≃ B ⊎ A
⊎-comm =
  record
    { to      = λ a⊎b → ⊎-swap a⊎b
    ; from    = λ b⊎a → ⊎-swap b⊎a
    ; from∘to = λ a⊎b → ⊎-swap-elim a⊎b
    ; to∘from = λ b⊎a → ⊎-swap-elim b⊎a
    }
