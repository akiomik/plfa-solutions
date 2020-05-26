module ⊥-identityˡ where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Connectives using (_≃_; _⊎_; inj₁; inj₂; ⊥)

-- ⊥ の左恒等性の証明
⊥-identityˡ : ∀ {A : Set} → ⊥ ⊎ A ≃ A
⊥-identityˡ =
  record
    { to      = λ ⊥⊎a → ⊥-identityˡ-to ⊥⊎a
    ; from    = λ a → inj₂ a
    ; from∘to = λ ⊥⊎a → ⊥-identityˡ-from∘to ⊥⊎a
    ; to∘from = λ a → refl
    }
  where
    -- 射 f : X → Y
    ⊥-identityˡ-to : ∀ {A : Set}
      → ⊥ ⊎ A
        -----
      → A
    ⊥-identityˡ-to (inj₁ ())
    ⊥-identityˡ-to (inj₂ a) = a

    -- 左逆射 g ∘ f = id_X を持つことの証明
    ⊥-identityˡ-from∘to : ∀ {A : Set} → (x : ⊥ ⊎ A)
      → inj₂ (⊥-identityˡ-to x) ≡ x
    ⊥-identityˡ-from∘to (inj₁ ())
    ⊥-identityˡ-from∘to (inj₂ a) = refl
