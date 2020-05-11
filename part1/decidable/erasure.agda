module erasure where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import decidable using (Dec; yes; no; Bool; true; false; ⌊_⌋; _∧_; _×-dec_; _∨_; _⊎-dec_; not; ¬?)

-- erasureを使うことで真偽値の論理積とdecidableの論理積が等しくなることの証明
∧-× : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∧ ⌊ y ⌋ ≡ ⌊ x ×-dec y ⌋
∧-× (yes a) (yes b) = refl
∧-× (yes a) (no b)  = refl
∧-× (no a)  (yes b) = refl
∧-× (no a)  (no b)  = refl

-- erasureを使うことで真偽値の論理和とdecidableの論理和が等しくなることの証明
∨-⊎ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∨ ⌊ y ⌋ ≡ ⌊ x ⊎-dec y ⌋
∨-⊎ (yes a) (yes b) = refl
∨-⊎ (yes a) (no b)  = refl
∨-⊎ (no a)  (yes b) = refl
∨-⊎ (no a)  (no b)  = refl

-- erasureを使うことで真偽値の否定とdecidableの否定が等しくなることの証明
not-¬ : ∀ {A : Set} (x : Dec A) → not ⌊ x ⌋ ≡ ⌊ ¬? x ⌋
not-¬ (yes a) = refl
not-¬ (no a)  = refl
