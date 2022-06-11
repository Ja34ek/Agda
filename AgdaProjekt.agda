module AgdaProjekt where

open import level
open import bool
open import product
open import Equality
open import negation using (¬_)
open import AnyAll


postulate
    string : Set

{-# BUILTIN STRING string #-}


data D : Set where
    a : D 
    

data formula : Set where  --definicja 1.5
    var : string → formula
    varneq : string → formula
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



data _,_⊨_ : (k : struct) -> W k -> formula -> Set where
    B1 : ∀ ( k : struct ) → ∀ ( s : W k ) → ∀ ( p : string ) → ( V k ) p s ≡ tt → k , s ⊨ var p
    B2 : ∀ ( k : struct ) → ∀ ( s : W k ) → ∀ ( p : string ) → ( V k ) p s ≡ ff → k , s ⊨ varneq p --nawiasy sprawdzić
    B3 : ∀ ( k : struct ) → ∀ ( s : W k ) → k , s ⊨ Truee
    B4 : ∀ ( k : struct ) → ∀ ( s : W k ) → ∀ ( ϕ ψ : formula ) → k , s ⊨ ϕ → k , s ⊨ ψ → k , s ⊨ And ϕ ψ
    B5 : ∀ ( k : struct ) → ∀ ( s : W k ) → ∀ ( ϕ ψ : formula ) → k , s ⊨ ψ → k , s ⊨ Or ϕ ψ
    B6 : ∀ ( k : struct ) → ∀ ( s : W k ) → ∀ ( ϕ ψ : formula ) → k , s ⊨ ϕ → k , s ⊨ Or ϕ ψ
    B7 : ∀ ( k : struct ) → ∀ ( s : W k ) → ∀ ( ϕ : formula ) → ∀ ( d : D ) → ( ∀ (t : W k ) → ( R k ) s d t ≡ tt → k , t ⊨ ϕ ) → k , s ⊨ □ d ϕ 
    B8 : ∀ ( k : struct ) → ∀ ( s : W k ) → ∀ ( ϕ : formula ) → ∀ ( d : D ) → ( t : W k ) → ( R k ) s d t ≡ tt →  k , t ⊨ ϕ →  k , s ⊨ ⋄ d ϕ

-- _,_⊨ᵇ_ : (k : struct) -> W k -> formula -> 𝔹
-- S , s ⊨ᵇ var x = V S x s
-- S , s ⊨ᵇ Truee = tt
-- S , s ⊨ᵇ And ϕ ϕ₁ = S , s ⊨ᵇ ϕ && S , s ⊨ᵇ ϕ₁
-- S , s ⊨ᵇ Or ϕ ϕ₁ = S , s ⊨ᵇ ϕ || S , s ⊨ᵇ ϕ₁
-- S , s ⊨ᵇ ⋄ x ϕ = {!   !}
-- S , s ⊨ᵇ □ x ϕ with ( ∀ (t : W S ) → ( R S ) s x t ≡ tt )
-- ...         | tt ( ∀ (t : W S ) → ( R S ) s x t ≡ tt ) = ?
-- ...         | ff ( ∀ (t : W S ) → ( R S ) s x t ≡ tt ) = ?


data _,_≣'_,_ : (S : struct) → ( s : W S ) → (S' : struct) → ( s' : W S' ) → Set where
    var1 : ( S S' : struct ) → ( s : W S ) → ( s' : W S' ) →  ∀ ( ϕ : formula ) → S , s ⊨ ϕ → S' , s' ⊨ ϕ → S , s ≣' S' , s'


data _,_≣_,_ : (S : struct) → ( s : W S ) → (S' : struct) → ( s' : W S' ) → Set where
    var1 : ( S S' : struct ) → ( s : W S ) → ( s' : W S' ) →  ∀ ( ϕ : formula ) → S , s ≣' S' , s' →  S' , s' ≣' S , s → S , s ≣ S' , s'

data _,_prop_,_ :  (S : struct) → ( s : W S ) → (S' : struct) → ( s' : W S' ) → Set where
    var1 :  ( S S' : struct ) → ( s : W S ) → ( s' : W S' ) → ∀ ( p : string ) → ((( V S ) p s ) iff (( V S' ) p s' )) ≡ tt → S , s prop S' , s'

data _,_forth_,_,_ :  (S : struct) → ( s : W S ) → (S' : struct) → ( s' : W S' ) → (Z : List ( W S × W S')) → Set where
    var1 : ( S S' : struct ) → ( s : W S ) → ( s' : W S' ) → (Z : List ( (W S) × (W S') )) → ∀ (d : D) → ∀ (t : W S ) → ( R S ) s d t ≡ tt → (t' : W S' ) → ( R S' ) s' d t' ≡ tt → (t , t') ∈ Z → S , s forth S' , s' , Z

data _,_back_,_,_ :  (S : struct) → ( s : W S ) → (S' : struct) → ( s' : W S' ) → (Z : List ( W S × W S')) → Set where
    var1 : ( S S' : struct ) → ( s : W S ) → ( s' : W S' ) → (Z : List ( (W S) × (W S') )) → ∀ (d : D) → ∀ (t' : W S' ) → ( R S' ) s' d t' ≡ tt → (t : W S ) → ( R S ) s d t ≡ tt → (t , t') ∈ Z → S , s back S' , s' , Z

data  _,_↔_,_ : (S : struct) → ( s : W S ) → (S' : struct) → ( s' : W S' ) → Set where
    v1 : ( S S' : struct ) → ( s : W S ) → ( s' : W S' ) → ∀ ( p : string ) → (Z : List ( (W S) × (W S') )) → S , s prop S' , s' → S , s forth S' , s' , Z → S , s back S' , s' , Z → S , s ↔ S' , s'

-- H-M_theorem 




data World : Set where
    w0 : World
    w1 : World
    w2 : World


Rel :  World → D → World → 𝔹
Rel w0 a w0 = ff
Rel w0 a w1 = tt
Rel w0 a w2 = ff 
Rel w1 a w0 = ff
Rel w1 a w1 = ff
Rel w1 a w2 = tt
Rel w2 a w0 = tt
Rel w2 a w1 = ff 
Rel w2 a w2 = tt 

Val : string → World → 𝔹 
Val "p" w0 = tt 
Val "q" w0 = ff
Val "p" w1 = ff 
Val "q" w1 = tt
Val "p" w2 = tt 
Val "q" w2 = tt
Val _ _ = ff

    
S : struct
S = record { W = World ; R = Rel ; V = Val }


example1 : S , w0 ⊨ ( var "p" )
example1 = B1 S w0 "p" refl

example2 : S , w1 ⊨ (varneq "p")
example2 = B2 S w1 "p" refl

example3 : S , w0 ⊨ Truee
example3 = B3 S w0

example4 : S , w2 ⊨ And (var "p") (var "q")
example4 = B4 S w2 (var "p") (var "q") (B1 S w2 "p" refl) (B1 S w2 "q" refl)

example5 : S , w0 ⊨ Or (var "p") (var "q")
example5 = B6 S w0 (var "p") (var "q") (B1 S w0 "p" refl) 

example6 : S , w2 ⊨ ⋄ a (var "p")
example6 = B8 S w2 (var "p") a w0 refl (B1 S w0 "p" refl)

example7 : S , w1 ⊨ □ a (var "q")
example7 = B7 S w1 (var "q") a λ t x → B1 S t "q" {! (V S) "q" t ≡ tt !} 