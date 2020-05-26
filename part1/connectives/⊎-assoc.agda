module ⊎-assoc where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Connectives using (_≃_; _⊎_; inj₁; inj₂)

-- 直和の結合律が同型であることの証明
⊎-assoc : ∀ {A B C : Set} → (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
⊎-assoc =
  record
    { to      = ⊎-assoc-to
    ; from    = ⊎-assoc-from
    ; from∘to = ⊎-assoc-from∘to
    ; to∘from = ⊎-assoc-to∘from
    }
  where
    -- 直和の結合律の射 f : X → Y
    ⊎-assoc-to : ∀ {A B C : Set}
      → (A ⊎ B) ⊎ C
        -----------
      → A ⊎ (B ⊎ C)
    ⊎-assoc-to (inj₁ (inj₁ a)) = inj₁ a
    ⊎-assoc-to (inj₁ (inj₂ b)) = inj₂ (inj₁ b)
    ⊎-assoc-to (inj₂ c)        = inj₂ (inj₂ c)

    -- 直和の結合律の射 g : Y → X
    ⊎-assoc-from : ∀ {A B C : Set}
      → A ⊎ (B ⊎ C)
        -----------
      → (A ⊎ B) ⊎ C
    ⊎-assoc-from (inj₁ a)        = inj₁ (inj₁ a)
    ⊎-assoc-from (inj₂ (inj₁ b)) = inj₁ (inj₂ b)
    ⊎-assoc-from (inj₂ (inj₂ c)) = inj₂ c

    -- 直和の結合律が左逆射 g ∘ f = id_X を持つことの証明
    ⊎-assoc-from∘to : ∀ {A B C : Set} → (w : ((A ⊎ B) ⊎ C))
      → ⊎-assoc-from (⊎-assoc-to w) ≡ w
    ⊎-assoc-from∘to (inj₁ (inj₁ a)) = refl
    ⊎-assoc-from∘to (inj₁ (inj₂ b)) = refl
    ⊎-assoc-from∘to (inj₂ c)        = refl

    -- 直和の結合律が右逆射 f ∘ g = id_Y を持つことの証明
    ⊎-assoc-to∘from : ∀ {A B C : Set} → (w : (A ⊎ (B ⊎ C)))
      → ⊎-assoc-to (⊎-assoc-from w) ≡ w
    ⊎-assoc-to∘from (inj₁ a)        = refl
    ⊎-assoc-to∘from (inj₂ (inj₁ b)) = refl
    ⊎-assoc-to∘from (inj₂ (inj₂ c)) = refl
