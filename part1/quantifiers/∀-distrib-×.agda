module ∀-distrib-× where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
-- open import plfa.part1.Isomorphism using (_≃_; extensionality)

-- 同型 (isomorphism)
infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
open _≃_

-- 全称量化子の分配性の証明
∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
∀-distrib-× =
  record
    { to = λ h → ⟨ (λ x → proj₁ (h x)) , (λ x → proj₂ (h x)) ⟩
    ; from = λ (⟨ hˡ , hʳ ⟩) → λ{ x → ⟨ hˡ x , hʳ x ⟩ }
    ; from∘to = λ h → refl
    ; to∘from = λ hˡ×hʳ → refl
    }
