module iff-erasure where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥-elim)
-- open import plfa.part1.Isomorphism using (_⇔_)

-- 同値 (equivalence)
record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
open _⇔_

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

-- 必要十分条件 (if and only if)
_iff_ : Bool → Bool → Bool
true  iff true  = true
true  iff false = false
false iff true  = false
false iff false = true

-- 同値のdecidable
_⇔-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⇔ B)
yes a ⇔-dec yes b = yes record { to = λ _ → b ; from = λ _ → a }
yes a ⇔-dec no ¬b = no λ a⇔b → ¬b (to a⇔b a)
no ¬a ⇔-dec yes b = no λ a⇔b → ¬a (from a⇔b b)
no ¬a ⇔-dec no ¬b = yes record { to = λ a → ⊥-elim (¬a a) ; from = λ b → ⊥-elim (¬b b) }

-- erasureを使うことで真偽値の必要十分条件とdecidableの同値が等しくなることの証明
iff-⇔ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ iff ⌊ y ⌋ ≡ ⌊ x ⇔-dec y ⌋
iff-⇔ (yes a) (yes b) = refl
iff-⇔ (yes a) (no b)  = refl
iff-⇔ (no a)  (yes b) = refl
iff-⇔ (no a)  (no b)  = refl
