module ∃-⊎ where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)

open import Quantifiers using (_≃_; ⟨_,_⟩; ∃-syntax)
open import ∀-× using (Tri; aa; bb; cc)

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
∃-⊎-from∘to : {B : Tri → Set} → (e : ∃[ x ] B x) → (∃-⊎-from ∘ ∃-⊎-to) e ≡ e
∃-⊎-from∘to (⟨ aa , bx ⟩) = refl
∃-⊎-from∘to (⟨ bb , bx ⟩) = refl
∃-⊎-from∘to (⟨ cc , bx ⟩) = refl

-- 右逆射 f ∘ g = id_Y を持つことの証明
∃-⊎-to∘from : {B : Tri → Set} → (tri : B aa ⊎ B bb ⊎ B cc) → (∃-⊎-to (∃-⊎-from {B} tri)) ≡ tri
∃-⊎-to∘from (inj₁ baa)        = refl
∃-⊎-to∘from (inj₂ (inj₁ bbb)) = refl
∃-⊎-to∘from (inj₂ (inj₂ bcc)) = refl

-- ∃-⊎の証明
∃-⊎ : {B : Tri → Set} → (∃[ x ] B x) ≃ (B aa ⊎ B bb ⊎ B cc)
∃-⊎ =
  record
    { to      = ∃-⊎-to
    ; from    = ∃-⊎-from
    ; from∘to = ∃-⊎-from∘to
    ; to∘from = ∃-⊎-to∘from
    }
