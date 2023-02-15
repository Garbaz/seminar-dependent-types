-- {-# OPTIONS --type-in-type #-}

data Zero : Set0 where

One : Set1
One = Zero → Set

Two : Set2
Two = Zero → One → Set1

𝟙 : One
𝟙 x = Zero

𝟚₁ : Two
𝟚₁ _ _ = One

𝟚₂ : Two
𝟚₂ x y = {! y x  !}