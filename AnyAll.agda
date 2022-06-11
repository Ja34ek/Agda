module AnyAll where

open import bool
open import Equality
open import negation using (¬_)
open import nat


data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

data Any {A : Set} (P : A → Set) : List A → Set where
  here  : ∀ {x : A} {xs : List A} → P x → Any P (x ∷ xs)
  there : ∀ {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)



data All {A : Set} (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : ∀ {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)



_∈_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∈ xs = Any (_≡ x) xs 




data Reflects {p} (P : Set p) : 𝔹 → Set p where
  ofʸ : ( p :   P) → Reflects P tt
  ofⁿ : (¬p : ¬ P) → Reflects P ff

record Dec {p} (P : Set p) : Set p where
  constructor _because_
  field
    does  : 𝔹
    proof : Reflects P does

Decidable : ∀ {A : Set} → (A → Set) → Set
Decidable {A} P  =  ∀ (x : A) → Dec (P x)

pattern yes p =  tt because ofʸ  p
pattern no ¬p = ff because ofⁿ ¬p

  
All? : ∀ {A : Set} {P : A → Set} → Decidable P → Decidable (All P)
All? P? []                                 =  yes []
All? P? (x ∷ xs) with P? x   | All? P? xs
...                 | yes Px | yes Pxs     =  yes (Px ∷ Pxs)
...                 | no ¬Px | _           =  no λ{ (Px ∷ Pxs) → ¬Px Px   }
...                 | _      | no ¬Pxs     =  no λ{ (Px ∷ Pxs) → ¬Pxs Pxs }


-- Any? : ∀ {A : Set} {P : A → Set} → Decidable P → Decidable (Any P)
-- Any? P? here                                 =  yes here
-- Any? P? (x ∷ xs) with P? x   | Any? P? xs
-- ...                 | yes Px | yes Pxs     =  yes (Px ∷ Pxs)
-- ...                 | no ¬Px | _           =  no λ{ (Px ∷ Pxs) → ¬Px Px   }
-- ...                 | _      | no ¬Pxs     =  no λ{ (Px ∷ Pxs) → ¬Pxs Pxs }

{-# BUILTIN LIST List #-}

pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []

_ : 2 ∈ [ 0 , 1 , 0 , 2 ]
_ = there (there (there (here refl)))
