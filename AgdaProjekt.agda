module AgdaProjekt where

open import level
open import bool
open import product
open import Equality

postulate
    string : Set
    A : Set
    _≥A_ : A → A → Set 
    

data D : Set where
    a : D 
    b : D


-- infix 4 _∈_ _∉_

-- data Any {A : Set} (P : A → Set) : List A → Set where
--     here  : ∀ {x : A} {xs : List A} → P x → Any P (x ∷ xs)
--     there : ∀ {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)

-- _∈_ : ∀ {A : Set} (x : A) (xs : List A) → Set
--     x ∈ xs = Any (x ≡_) xs

-- _∉_ : ∀ {A : Set} (x : A) (xs : List A) → Set
--     x ∉ xs = ¬ (x ∈ xs)

data formula : Set where  --definicja 1.5
    var : string → formula
    Truee : formula 
    And : formula → formula → formula
    Or : formula → formula → formula
    ⋄ : D → formula → formula
    □ : D → formula → formula


record struct : Set1 where
    field   W         : Set 
            R         : W → D → W → 𝔹
            V         : string → W → 𝔹
open struct


-- data _Z_ : {S S' : struct} → W S → W S' → 𝔹 where





data _,_⊨_ : (k : struct) -> W k -> formula -> Set where
    B1 : ∀ ( k : struct ) → ∀ ( s : W k ) → ∀ ( p : string ) → ( V k ) p s ≡ tt → k , s ⊨ var p
    Bezu61 : ∀ ( k : struct ) → ∀ ( s : W k ) → ∀ ( p : string ) → ( V k ) p s ≡ ff → k , s ⊨ var p
    Bezu62 : ∀ ( k : struct ) → ∀ ( s : W k ) → k , s ⊨ Truee
    Bezu63 : ∀ ( k : struct ) → ∀ ( s : W k ) → ∀ ( ϕ ψ : formula ) → k , s ⊨ ϕ → k , s ⊨ ψ → k , s ⊨ And ϕ ψ
    Bezu64a : ∀ ( k : struct ) → ∀ ( s : W k ) → ∀ ( ϕ ψ : formula ) → k , s ⊨ ψ → k , s ⊨ Or ϕ ψ
    Bezu64b : ∀ ( k : struct ) → ∀ ( s : W k ) → ∀ ( ϕ ψ : formula ) → k , s ⊨ ϕ → k , s ⊨ Or ϕ ψ
    Bezu65a : ∀ ( k : struct ) → ∀ ( s : W k ) → ∀ ( ϕ : formula ) → ∀ ( d : D ) → ( ∀ (t : W k ) → ( R k ) s d t ≡ tt → k , t ⊨ ϕ ) → k , s ⊨ □ d ϕ 
    Bezu66a : ∀ ( k : struct ) → ∀ ( s : W k ) → ∀ ( ϕ : formula ) → ∀ ( d : D ) → ( t : W k ) → ( R k ) s d t ≡ tt →  k , t ⊨ ϕ →  k , s ⊨ ⋄ d ϕ



data _,_≣'_,_ : (S : struct) → ( s : W S ) → (S' : struct) → ( s' : W S' ) → Set where
    var1 : ( S S' : struct ) → ( s : W S ) → ( s' : W S' ) →  ∀ ( ϕ : formula ) → S , s ⊨ ϕ → S' , s' ⊨ ϕ → S , s ≣' S' , s'


data _,_≣_,_ : (S : struct) → ( s : W S ) → (S' : struct) → ( s' : W S' ) → Set where
    var1 : ( S S' : struct ) → ( s : W S ) → ( s' : W S' ) →  ∀ ( ϕ : formula ) → S , s ≣' S' , s' →  S' , s' ≣' S , s → S , s ≣ S' , s'

data _,_prop_,_ :  (S : struct) → ( s : W S ) → (S' : struct) → ( s' : W S' ) → Set where
    var1 :  ( S S' : struct ) → ( s : W S ) → ( s' : W S' ) → ∀ ( p : string ) → ((( V S ) p s ) iff (( V S' ) p s' )) ≡ tt → S , s prop S' , s'

-- data _,_forth_,_ :  (S : struct) → ( s : W S ) → (S' : struct) → ( s' : W S' ) → Set where
--     var1 : (S S' : struct ) → ( s : W S ) → ( s' : W S' ) → ∀ (d : D) → ∀ (t : W S ) → ( R S ) s d t ≡ tt → (t' : W S' ) → ( R S' ) s' d t' ≡ tt 


-- module ⊨-example1 where
--     {-# BUILTIN STRING string #-}
--     data worlds : Set where  --swiaty
--         w1 : worlds
--         w2 : worlds
--         w3 : worlds
--         w4 : worlds
--         w5 : worlds
--     data relations : worlds → worlds → Set where --relacja dostepnosci
--         r11 : relations w1 w1
--         r12 : relations w1 w2
--         r13 : relations w1 w3
--         r34 : relations w3 w4
--         r45 : relations w4 w5
--         r53 : relations w5 w3
--     data valuations : worlds → string → Set where  --funkcja V
--         v1p : valuations w1 "p" 
--         v1q : valuations w1 "q" 
--         v2p : valuations w2 "p" 
--         v2r : valuations w2 "r" 
--         v3p : valuations w3 "p" 
--         v3q : valuations w3 "q" 
--         v3r : valuations w3 "r" 
--         v4p : valuations w4 "p" 
--         v4x : valuations w4 "x"
--         v5q : valuations w5 "q" 
--         v5y : valuations w5 "y" 

--     k : struct
--     k = record { W = worlds ; R = relations ; V = valuations }


 
 