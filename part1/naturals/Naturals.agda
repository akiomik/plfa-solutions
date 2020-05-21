module Naturals where

-- The naturals are an inductive datatype

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
