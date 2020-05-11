module product where

open import Data.Nat using (ℕ; _*_)
open import lists using (List; foldr)

-- リストの要素の積
product : (List ℕ) → ℕ
product xs = foldr _*_ 1 xs
