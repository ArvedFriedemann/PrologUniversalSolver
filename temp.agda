{-# OPTIONS --overlapping-instances #-}
module temp where

open import Agda.Primitive renaming (_⊔_ to _~U~_)

variable
  l l1 l2 l3 l4 : Level
  A B C D : Set l

data <U> : Set where
  one : <U>

data exists (A : Set l) (B : A -> Set l) : Set l where
  instance
    prf : {a : A} -> {{_ : B a}} -> exists A B

cert : {A : Set l} {B : A -> Set l} -> exists A B -> A
cert (prf {a} {{_}}) = a

infixr 4 _::_
data List (A : Set l) : Set l where
  [] : List A
  _::_ : A -> List A -> List A

data Concat {A : Set l} : List A -> List A -> List A -> Set l where
  instance
    concat-base : {L2 : List A} -> Concat [] L2 L2
    concat-rec : {X : A} -> {XS ZS B : List A} -> {{_ : Concat XS B ZS}} -> Concat (X :: XS) B (X :: ZS)

test : Concat (one :: one :: []) (one :: []) (one :: one :: one :: [])
test = concat-rec

test2 : exists (List <U>) (\X -> Concat (one :: one :: []) (one :: []) X)
test2 = prf

test3 : List <U>
test3 = cert test2
