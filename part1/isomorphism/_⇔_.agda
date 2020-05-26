module _⇔_ where

open import Isomorphism using (_∘_)

record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
open _⇔_

-- 反射性
⇔-refl : ∀ {A : Set}
    -----
  → A ⇔ A
⇔-refl =
  record
    { to   = λ{x → x}
    ; from = λ{y → y}
    }

-- 対称性
⇔-sym : ∀ {A B : Set}
  → A ⇔ B
    -----
  → B ⇔ A
⇔-sym A⇔B =
  record
    { to   = from A⇔B
    ; from = to A⇔B
    }

-- 推移性
⇔-trans : ∀ {A B C : Set}
  → A ⇔ B
  → B ⇔ C
    -----
  → A ⇔ C
⇔-trans A⇔B B⇔C =
  record
    { to   = to B⇔C   ∘ to A⇔B
    ; from = from A⇔B ∘ from B⇔C
    }
