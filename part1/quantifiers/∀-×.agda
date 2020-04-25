module ∀-× where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)
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

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

postulate
  -- 外延性の公理 (Tri版)
  extensionality-tri : ∀ {B : Tri → Set} → (f g : ∀ (x : Tri) → B x)
    → (∀ (x : Tri) → f x ≡ g x)
    → f ≡ g

∀-×-to : {B : Tri → Set} → (∀ (x : Tri) → B x) → (B aa × B bb × B cc)
∀-×-to f = ⟨ f aa , ⟨ f bb , f cc ⟩ ⟩

∀-×-from : {B : Tri → Set} → (B aa × B bb × B cc) → (∀ (x : Tri) → B x)
∀-×-from (⟨ baa , ⟨ bbb , bcc ⟩ ⟩) =
  λ{ aa → baa
   ; bb → bbb
   ; cc → bcc
   }

∀-×-from∘to : {B : Tri → Set} → (f : ∀ (x : Tri) → B x) →
  (∀-×-from ∘ ∀-×-to) f ≡ f
∀-×-from∘to f = extensionality-tri ((∀-×-from ∘ ∀-×-to) f) f λ{ aa → refl; bb → refl; cc → refl}

-- Failed to solve constraints
-- ∀-×-to∘from : {B : Tri → Set} → (tri : (B aa × B bb × B cc)) → (∀-×-to (∀-×-from tri)) ≡ tri
-- ∀-×-to∘from (⟨ baa , ⟨ bbb , bcc ⟩ ⟩) = refl

∀-× : {B : Tri → Set} →
  (∀ (x : Tri) → B x) ≃ (B aa × B bb × B cc)
∀-× =
  record
    { to      = ∀-×-to
    ; from    = ∀-×-from
    ; from∘to = ∀-×-from∘to
    ; to∘from = λ (⟨ baa , ⟨ bbb , bcc ⟩ ⟩) → refl
    }
