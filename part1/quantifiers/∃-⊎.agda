module ∃-⊎ where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Sum using (_⊎_; inj₁; inj₂)
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

-- 依存和型 (dependent sum type)
data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B

-- 存在量化子 (existential quantifier)
∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

-- 射 f : X → Y
∃-⊎-to : {B : Tri → Set} → (∃[ x ] B x) → (B aa ⊎ B bb ⊎ B cc)
∃-⊎-to (⟨ aa , bx ⟩) = inj₁ bx
∃-⊎-to (⟨ bb , bx ⟩) = inj₂ (inj₁ bx)
∃-⊎-to (⟨ cc , bx ⟩) = inj₂ (inj₂ bx)

-- 射 g : Y → X
∃-⊎-from : {B : Tri → Set} → (B aa ⊎ B bb ⊎ B cc) → (∃[ x ] B x)
∃-⊎-from (inj₁ baa)        = ⟨ aa , baa ⟩
∃-⊎-from (inj₂ (inj₁ bbb)) = ⟨ bb , bbb ⟩
∃-⊎-from (inj₂ (inj₂ bcc)) = ⟨ cc , bcc ⟩

-- 左逆射 g ∘ f = id_X を持つことの証明
∃-⊎-from∘to : {B : Tri → Set} → (e : ∃[ x ] B x) →
  (∃-⊎-from ∘ ∃-⊎-to) e ≡ e
∃-⊎-from∘to (⟨ aa , bx ⟩) = refl
∃-⊎-from∘to (⟨ bb , bx ⟩) = refl
∃-⊎-from∘to (⟨ cc , bx ⟩) = refl

-- 右逆射 f ∘ g = id_Y を持つことの証明
∃-⊎-to∘from : {B : Tri → Set} → (tri : B aa ⊎ B bb ⊎ B cc) → (∃-⊎-to (∃-⊎-from {B} tri)) ≡ tri
∃-⊎-to∘from (inj₁ baa)        = refl
∃-⊎-to∘from (inj₂ (inj₁ bbb)) = refl
∃-⊎-to∘from (inj₂ (inj₂ bcc)) = refl

-- ∃-⊎の証明
∃-⊎ : {B : Tri → Set} →
  (∃[ x ] B x) ≃ (B aa ⊎ B bb ⊎ B cc)
∃-⊎ =
  record
    { to      = ∃-⊎-to
    ; from    = ∃-⊎-from
    ; from∘to = ∃-⊎-from∘to
    ; to∘from = ∃-⊎-to∘from
    }
