module split where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n; _≤?_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)

open import lists using (List; []; _∷_; [_]; [_,_]; [_,_,_]; [_,_,_,_]; All; Decidable)

-- リストのマージ
-- xs と ys を使って zs を組み立てる
data merge {A : Set} : (xs ys zs : List A) → Set where
  [] :
      --------------
      merge [] [] []

  left-∷ : ∀ {x xs ys zs}
    → merge xs ys zs
      --------------------------
    → merge (x ∷ xs) ys (x ∷ zs)

  right-∷ : ∀ {y xs ys zs}
    → merge xs ys zs
      --------------------------
    → merge xs (y ∷ ys) (y ∷ zs)

_ : merge [ 1 , 4 ] [ 2 , 3 ] [ 1 , 2 , 3 , 4 ]
_ = left-∷ (right-∷ (right-∷ (left-∷ [])))

-- リストの分割
-- 述語Pが成り立つ場合はxs、そうでない場合はysとして分割する (scalaでいうpartition)
split : ∀ {A : Set} {P : A → Set} (P? : Decidable P) (zs : List A)
  → ∃[ xs ] ∃[ ys ] (merge xs ys zs × All P xs × All (¬_ ∘ P) ys)
split P? []                                                                 = ⟨ [] ,     ⟨ [] ,     ⟨ [] ,        ⟨ [] ,       [] ⟩ ⟩ ⟩ ⟩
split P? (z ∷ zs) with P? z   | split P? zs
...                  | yes Pz | ⟨ xs , ⟨ ys , ⟨ m , ⟨ Pxs , ¬Pys  ⟩  ⟩  ⟩ ⟩ = ⟨ z ∷ xs , ⟨ ys ,     ⟨ left-∷ m ,  ⟨ Pz ∷ Pxs , ¬Pys ⟩ ⟩ ⟩ ⟩
...                  | no ¬Pz | ⟨ xs , ⟨ ys , ⟨ m , ⟨ Pxs , ¬Pys  ⟩  ⟩  ⟩ ⟩ = ⟨ xs ,     ⟨ z ∷ ys , ⟨ right-∷ m , ⟨ Pxs ,      ¬Pz ∷ ¬Pys ⟩ ⟩ ⟩ ⟩

-- 0と等しい1以上の自然数は存在しない
¬z≡n : ∀ {n : ℕ} → ¬ (zero ≡ suc n)
¬z≡n ()

-- m = n が成り立たなければ (m + 1) = (n + 1) も成り立たない
¬s≡s : ∀ {m n : ℕ} → ¬ (m ≡ n) → ¬ (suc m ≡ suc n)
¬s≡s ¬m≡n refl = ¬m≡n refl

-- decidableを使った、2つの自然数が等しいかどうか判定する関数
_≡ℕ?_ : ∀ (m n : ℕ) → Dec (m ≡ n)
zero  ≡ℕ? zero                = yes refl
zero  ≡ℕ? suc n               = no ¬z≡n
suc m ≡ℕ? zero                = no (λ ())
suc m ≡ℕ? suc n with m ≡ℕ? n
...                | yes refl = yes refl
...                | no ¬m≡n  = no (¬s≡s ¬m≡n)

-- テスト
-- リストの要素を3とそれ以外とに分ける
_ : split (_≡ℕ? 3) [ 3 , 0 , 3 , 1 ]
  ≡ ⟨ [ 3 , 3 ] , ⟨ [ 0 , 1 ] , ⟨ (left-∷ (right-∷ (left-∷ (right-∷ [])))) , ⟨ refl ∷ refl ∷ [] , ¬z≡n ∷ (¬s≡s ¬z≡n) ∷ [] ⟩ ⟩ ⟩ ⟩ 
_ = refl
