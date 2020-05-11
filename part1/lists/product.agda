module product where

open import Data.Nat using (ℕ; _*_)

-- リスト
infixr 5 _∷_
data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

-- 右畳み込み
foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr _⊗_ e []       = e
foldr _⊗_ e (x ∷ xs) = x ⊗ foldr _⊗_ e xs

-- リストの要素の積
product : (List ℕ) → ℕ
product xs = foldr _*_ 1 xs
