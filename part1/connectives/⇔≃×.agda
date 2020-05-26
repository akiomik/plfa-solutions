module ⇔≃× where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning

open import Connectives using (_≃_; _×_; ⟨_,_⟩; proj₁; proj₂; η-×)

-- 同値 (必要十分条件: iff)
infix 1 _⇔_
record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
open _⇔_

-- A ⇔ B と (A → B) × (B → A) が同型であることの証明
⇔≃× : ∀ {A B : Set} → (A ⇔ B) ≃ ((A → B) × (B → A))
⇔≃× =
  record
    { to      = λ a⇔b → ⟨ to a⇔b , from a⇔b ⟩
    ; from    = λ ab×ba → record { to   = proj₁ ab×ba
                                 ; from = proj₂ ab×ba }
    ; from∘to = λ a⇔b → refl
    ; to∘from = λ ab×ba →
      begin
        ⟨ to   record { to = proj₁ ab×ba ; from = proj₂ ab×ba }
        , from record { to = proj₁ ab×ba ; from = proj₂ ab×ba } ⟩
      ≡⟨⟩
        ⟨ proj₁ ab×ba , proj₂ ab×ba ⟩
      ≡⟨ η-× ab×ba ⟩
        ab×ba
      ∎
    }
