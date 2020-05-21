module seven where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Naturals using (ℕ; zero; suc)

seven : ℕ
seven = suc (suc (suc (suc (suc (suc (suc zero))))))

_ : seven ≡ 7
_ = refl
