module ⊥-identityʳ where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Connectives using (_≃_; _⊎_; inj₁; inj₂; ⊥)

-- ⊥ の右恒等性の証明
⊥-identityʳ : ∀ {A : Set} → A ⊎ ⊥ ≃ A
⊥-identityʳ =
  record
    { to      = λ a⊎⊥ → ⊥-identityʳ-to a⊎⊥
    ; from    = λ a → inj₁ a
    ; from∘to = λ a⊎⊥ → ⊥-identityʳ-from∘to a⊎⊥
    ; to∘from = λ a → refl
    }
  where
    -- 射 f : X → Y
    ⊥-identityʳ-to : ∀ {A : Set}
      → A ⊎ ⊥
        -----
      → A
    ⊥-identityʳ-to (inj₁ a) = a
    ⊥-identityʳ-to (inj₂ ())

    -- 左逆射 g ∘ f = id_X を持つことの証明
    ⊥-identityʳ-from∘to : ∀ {A : Set} → (x : A ⊎ ⊥)
      → inj₁ (⊥-identityʳ-to x) ≡ x
    ⊥-identityʳ-from∘to (inj₁ a) = refl
    ⊥-identityʳ-from∘to (inj₂ ())
