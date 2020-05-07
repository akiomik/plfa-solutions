module erasure where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using () renaming (contradiction to ¬¬-intro)

-- decidable
data Dec (A : Set) : Set where
  yes :   A → Dec A
  no  : ¬ A → Dec A

-- 真偽値 (boolean)
data Bool : Set where
  true  : Bool
  false : Bool

-- erasure
⌊_⌋ : ∀ {A : Set} → Dec A → Bool
⌊ yes x ⌋ = true
⌊ no ¬x ⌋ = false

-- 真偽値の論理積
infixr 6 _∧_
_∧_ : Bool → Bool → Bool
true  ∧ true  = true
false ∧ _     = false
_     ∧ false = false

-- decidableの論理積
infixr 6 _×-dec_
_×-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A × B)
yes x ×-dec yes y = yes ⟨ x , y ⟩
no ¬x ×-dec _     = no λ{ ⟨ x , y ⟩ → ¬x x }
_     ×-dec no ¬y = no λ{ ⟨ x , y ⟩ → ¬y y }

-- 真偽値の論理和
infixr 5 _∨_
_∨_ : Bool → Bool → Bool
true  ∨ _     = true
_     ∨ true  = true
false ∨ false = false

-- decidableの論理和
infixr 5 _⊎-dec_
_⊎-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⊎ B)
yes x ⊎-dec _     = yes (inj₁ x)
_     ⊎-dec yes y = yes (inj₂ y)
no ¬x ⊎-dec no ¬y = no λ{ (inj₁ x) → ¬x x ; (inj₂ y) → ¬y y }

-- 真偽値の否定
not : Bool → Bool
not true  = false
not false = true

-- decidableの否定
¬? : ∀ {A : Set} → Dec A → Dec (¬ A)
¬? (yes x) = no (¬¬-intro x)
¬? (no ¬x) = yes ¬x

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
