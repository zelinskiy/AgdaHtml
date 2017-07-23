module Вспомогательные_определения where

{- Вспомогательные определения. Список, Строка, _≡_, Σ - без учета универсумов -}

Множество = Set

data ℕ : Set where
  нуль : ℕ
  след : ℕ → ℕ

{-# BUILTIN NATURAL ℕ  #-}



infixr 5 _∷_
data Список (A : Set) : Множество where
  []  : Список A
  _∷_ : A → Список A → Список A

отобразить_на_ : ∀ {A B} → (A → B) → Список A → Список B
отобразить f на [] = []
отобразить f на (x ∷ xы) = f x ∷ отобразить f на xы

обмен : ∀{A} → ℕ → Список A → Список A
обмен 0 (x ∷ y ∷ xы) = (y ∷ x ∷ xы)
обмен (след n) (x ∷ xы) = x ∷ обмен n xы
обмен _ [] = []
обмен 0 xы = xы

postulate Строка : Множество

{-# BUILTIN STRING Строка #-}

primitive primStringAppend : Строка → Строка → Строка

infixl 2 _конкатенировать_
_конкатенировать_ : Строка → Строка → Строка
_конкатенировать_ = primStringAppend

infix 4 _≡_
data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  instance рефл : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL рефл #-}

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    пр₁ : A
    пр₂ : B пр₁

open Σ public

infix 2 ∃-syntax

∃-syntax : ∀ (A : Set) → (A → Set) → Set
∃-syntax = Σ

syntax ∃-syntax A (λ x → B) = ∃[ x ∈ A ] B
