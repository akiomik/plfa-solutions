module ∃-distrib-⊎ where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Quantifiers using (_≃_; ⟨_,_⟩; ∃-syntax)

-- 存在量化子の分配性の証明
∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set}
  → ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
∃-distrib-⊎ =
  record
    { to      = λ{ (⟨ x , (inj₁ b) ⟩) → inj₁ ⟨ x , b ⟩
                 ; (⟨ x , (inj₂ c) ⟩) → inj₂ ⟨ x , c ⟩ }
    ; from    = λ{ (inj₁ ⟨ x , b ⟩) → ⟨ x , (inj₁ b) ⟩
                 ; (inj₂ ⟨ x , c ⟩) → ⟨ x , (inj₂ c) ⟩ }
    ; from∘to = λ{ (⟨ x , (inj₁ b) ⟩) → refl
                 ; (⟨ x , (inj₂ c) ⟩) → refl }
    ; to∘from = λ{ (inj₁ ⟨ x , b ⟩) → refl
                 ; (inj₂ ⟨ x , c ⟩) → refl }
    }
