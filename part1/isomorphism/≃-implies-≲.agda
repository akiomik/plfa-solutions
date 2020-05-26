module ≃-implies-≲ where

open import Isomorphism using (_≃_; _≲_)
open _≃_

-- 同型ならば埋め込み
≃-implies-≲ : ∀ {A B : Set}
  → A ≃ B
    -----
  → A ≲ B
≃-implies-≲ A≃B =
  record
    { to = to A≃B
    ; from = from A≃B
    ; from∘to = from∘to A≃B
    }
