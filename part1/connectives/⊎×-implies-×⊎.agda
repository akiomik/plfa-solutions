module ⊎×-implies-×⊎ where

open import Connectives using (_⊎_; inj₁; inj₂; _×_; ⟨_,_⟩)

-- 逆はAとD・CとBの組み合わせで成り立たない
⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
⊎×-implies-×⊎ (inj₁ ⟨ a , b ⟩) = ⟨ inj₁ a , inj₁ b ⟩
⊎×-implies-×⊎ (inj₂ ⟨ c , d ⟩) = ⟨ inj₂ c , inj₂ d ⟩
