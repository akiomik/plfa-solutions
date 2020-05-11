module iff-erasure where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
-- open import plfa.part1.Isomorphism using (_⇔_)
open import decidable using (Dec; yes; no; Bool; true; false; ⌊_⌋)

-- 同値 (equivalence)
record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
open _⇔_

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
