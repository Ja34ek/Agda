module AgdaProjekt where

-- Literatura: Yde Venema, Lectures on the modal μ-calculus, 2020

--biblioteki pomocnicze
open import level
open import bool
open import product
open import Equality
open import negation using (¬_)
open import AnyAll


postulate
    string : Set

{-# BUILTIN STRING string #-}


--Zbiór D - będziemy przyjmować że jest jednoelementowy
data D : Set where
    d : D 
    
--Model Kripkiego
record struct : Set1 where
    field   W         : Set 
            R         : W → D → W → 𝔹
            V         : string → W → 𝔹
open struct


--definicja formuł
data formula : Set where  
    var : string → formula 
    varneq : string → formula 
    Truee : formula 
    And : formula → formula → formula 
    Or : formula → formula → formula 
    ⋄ : D → formula → formula 
    □ : D → formula → formula 


--definicja relacji ⊨
data _,_⊨_ : (k : struct) -> W k -> formula -> Set where
    proofvar : ( k : struct ) → ( s : W k ) → ( p : string ) → ( V k ) p s ≡ tt → k , s ⊨ var p
    proofvarneq : ( k : struct ) → ( s : W k ) → ( p : string ) → ( V k ) p s ≡ ff → k , s ⊨ varneq p 
    proofTruee : ( k : struct ) → ( s : W k ) → k , s ⊨ Truee
    proofAnd : ( k : struct ) → ( s : W k ) → ( ϕ ψ : formula ) → k , s ⊨ ϕ → k , s ⊨ ψ → k , s ⊨ And ϕ ψ
    proofOr1 : ( k : struct ) → ( s : W k ) → ( ϕ ψ : formula ) → k , s ⊨ ϕ → k , s ⊨ Or ϕ ψ
    proofOr2 : ( k : struct ) → ( s : W k ) → ( ϕ ψ : formula ) → k , s ⊨ ψ → k , s ⊨ Or ϕ ψ
    proof⋄ : ( k : struct ) → ( s : W k ) → ( ϕ : formula ) → ( d : D ) → ( t : W k ) → ( R k ) s d t ≡ tt →  k , t ⊨ ϕ →  k , s ⊨ ⋄ d ϕ
    proof□ : ( k : struct ) → ( s : W k ) → ( ϕ : formula ) → ( d : D ) → ( ∀ ( t : W k ) → ( R k ) s d t ≡ tt → k , t ⊨ ϕ ) → k , s ⊨ □ d ϕ 


--definicja relacji modalnej równoważności
data _,_≣'_,_ : (S : struct) → ( s : W S ) → (S' : struct) → ( s' : W S' ) → Set where
    proof≣' : ( S S' : struct ) → ( s : W S ) → ( s' : W S' ) → ( ∀ ( ϕ : formula ) → S , s ⊨ ϕ → S' , s' ⊨ ϕ ) → S , s ≣' S' , s'

data _,_≣'reverse_,_ : (S : struct) → ( s : W S ) → (S' : struct) → ( s' : W S' ) → Set where
    proof≣'reverse : ( S S' : struct ) → ( s : W S ) → ( s' : W S' ) → S , s ≣' S' , s' → ( ∀ ( ϕ : formula ) → S , s ⊨ ϕ → S' , s' ⊨ ϕ ) → S , s ≣'reverse S' , s'

data _,_≣_,_ : (S : struct) → ( s : W S ) → (S' : struct) → ( s' : W S' ) → Set where
    proof≣ : ( S S' : struct ) → ( s : W S ) → ( s' : W S' ) → ( ∀ ( ϕ : formula ) → S , s ≣' S' , s' →  S' , s' ≣' S , s ) → S , s ≣ S' , s'


--Definicje zapisujemy jako wnioskowanie w jedną stronę, a do niektórych dowodów będziemy potrzebowali odwrotnego rozumowania, więc posłużymy się następującymi postulatami
postulate
    ≣→≣'1 : (S : struct) → ( s : W S ) → (S' : struct) → ( s' : W S' ) → (S , s ≣ S' , s') → (S , s ≣' S' , s') 
    ≣→≣'2 : (S : struct) → ( s : W S ) → (S' : struct) → ( s' : W S' ) → (S , s ≣ S' , s') → (S' , s' ≣' S , s) 
    ≣'reverse1 : ( S S' : struct ) → ( s : W S ) → ( s' : W S' ) → S , s ≣' S' , s' → ( ϕ : formula ) → S , s ⊨ ϕ
    ≣'reverse2 : ( S S' : struct ) → ( s : W S ) → ( s' : W S' ) → S' , s' ≣' S , s → ( ϕ : formula ) → S' , s' ⊨ ϕ
    ⊨reverse : ( S : struct ) → ( s : W S ) → ( p : string ) → S , s ⊨ var p → ( V S ) p s ≡ tt
    ∈Z : (S S' : struct) → (s : W S) → (s' : W S') → (d : D) → (Z : List ( (W S) × (W S') ) ) → S , s ≣ S' , s' → (t : W S) → ( R S ) s d t ≡ tt → (t' : W S') → ( R S' ) s' d t' ≡ tt → (t , t') ∈ Z 

--definicja bisymulacji
data _,_prop1_,_ :  (S : struct) → ( s : W S ) → (S' : struct) → ( s' : W S' ) → Set where
    proofp1 :  ( S S' : struct ) → ( s : W S ) → ( s' : W S' ) → ∀ ( p : string ) → (( V S ) p s ) ≡ tt → ( V S' ) p s'  ≡ tt → S , s prop1 S' , s'

data _,_prop_,_ :  (S : struct) → ( s : W S ) → (S' : struct) → ( s' : W S' ) → Set where
    proofp :  ( S S' : struct ) → ( s : W S ) → ( s' : W S' ) → ∀ ( p : string ) → S , s prop1 S' , s' → S' , s' prop1 S , s → S , s prop S' , s'

data _,_forth_,_,_ :  (S : struct) → ( s : W S ) → (S' : struct) → ( s' : W S' ) → (Z : List ( W S × W S')) → Set where
    prooff : ( S S' : struct ) → ( s : W S ) → ( s' : W S' ) → (Z : List ( (W S) × (W S'))) → ∀ (d : D) → ( ∀ (t : W S ) → ( R S ) s d t ≡ tt → ((t' : W S' ) → ( R S' ) s' d t' ≡ tt  → (t , t') ∈ Z )) → S , s forth S' , s' , Z

data _,_back_,_,_ :  (S : struct) → ( s : W S ) → (S' : struct) → ( s' : W S' ) → (Z : List ( W S × W S')) → Set where
    proofb : ( S S' : struct ) → ( s : W S ) → ( s' : W S' ) → (Z : List ((W S) × (W S') )) → ∀ (d : D) → ( ∀ (t' : W S' ) → ( R S' ) s' d t' ≡ tt → (t : W S ) → ( R S ) s d t ≡ tt → (t , t') ∈ Z ) → S , s back S' , s' , Z

data  _,_↔_,_,_ : (S : struct) → ( s : W S ) → (S' : struct) → ( s' : W S' ) → (Z : List ( (W S) × (W S') )) → Set where
    proof↔ : ( S S' : struct ) → ( s : W S ) → ( s' : W S' ) → (Z : List ( (W S) × (W S'))) → ∀ ( p : string ) → S , s prop S' , s' → S , s forth S' , s' , Z → S , s back S' , s' , Z → S , s ↔ S' , s' , Z


-- Twierdzenie Hennessy-Milnera

--Dowód w "←" stronę
--A
←H-M_theorem_prop : (S : struct) → ( s : W S ) → (S' : struct) → ( s' : W S' ) → S , s ≣ S' , s' → S , s prop S' , s'
←H-M_theorem_prop = λ S s S' s' x → 
    proofp S S' s s' "p" (proofp1 S S' s s' "p" ( ⊨reverse S s "p" ( ≣'reverse1 S S' s s' ( ≣→≣'1 S s S' s' x )  (var "p")))
    (( ⊨reverse S' s' "p" ( ≣'reverse2 S S' s s' ( ≣→≣'2 S s S' s' x ) (var "p"))))) 
    ((proofp1 S' S s' s "p" ( ⊨reverse S' s' "p" ( ≣'reverse2 S S' s s' ( ≣→≣'2 S s S' s' x ) (var "p"))) 
    (( ⊨reverse S s "p" ( ≣'reverse1 S S' s s' ( ≣→≣'1 S s S' s' x ) (var "p"))))))

--B
←H-M_theorem_forth : (S : struct) → ( s : W S ) → (S' : struct) → ( s' : W S' ) → (Z : List ( W S × W S')) → S , s ≣ S' , s' → S , s forth S' , s' , Z
←H-M_theorem_forth = λ S s S' s' Z x → prooff S S' s s' Z d (λ t x₁ t' x₂ → ∈Z S S' s s' d Z x t x₁ t' x₂)

--C
←H-M_theorem_back : (S : struct) → ( s : W S ) → (S' : struct) → ( s' : W S' ) → (Z : List ( W S × W S')) → S , s ≣ S' , s' → S , s back S' , s' , Z
←H-M_theorem_back = λ S s S' s' Z x →  proofb S S' s s' Z d λ t' x₁ t x₂ → ∈Z S S' s s' d Z x t x₂ t' x₁ 

-- Twierdzenie Hennessy-Milnera w "←" stronę

←H-M_theorem : (S : struct) → ( s : W S ) → (S' : struct) → ( s' : W S' ) → (Z : List ((W S) × (W S'))) → S , s ≣ S' , s' → S , s ↔ S' , s' , Z
←H-M_theorem = λ S s S' s' Z x → proof↔ S S' s s' Z "p" (←H-M_theorem_prop S s S' s' x) (←H-M_theorem_forth S s S' s' Z x) (←H-M_theorem_back S s S' s' Z x)


-- Twierdzenie Hennessy-Milnera w "→" stronę
→H-M_theorem : (S : struct) → ( s : W S ) → (S' : struct) → ( s' : W S' ) → (Z : List ((W S) × (W S'))) → S , s ↔ S' , s' , Z → S , s ≣ S' , s'
→H-M_theorem = λ S s S' s' Z x → proof≣ S S' s s' (λ ϕ x₁ → proof≣' S' S s' s λ ϕ₁ x₂ → ≣'reverse1 S S' s s' x₁ ϕ₁)



--Przykład nr 1
module ⊨-example1 where

    data World : Set where
        w0 : World
        w1 : World
        w2 : World

    Rel : World → D → World → 𝔹
    Rel w0 d w0 = ff
    Rel w0 d w1 = tt
    Rel w0 d w2 = ff 
    Rel w1 d w0 = ff
    Rel w1 d w1 = ff
    Rel w1 d w2 = tt
    Rel w2 d w0 = tt
    Rel w2 d w1 = ff 
    Rel w2 d w2 = tt 

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

    --Dowody wybranych własności
    _ : S , w0 ⊨ ( var "p" )
    _ = proofvar S w0 "p" refl

    _ : S , w1 ⊨ (varneq "p")
    _ = proofvarneq S w1 "p" refl

    _ : S , w0 ⊨ Truee
    _ = proofTruee S w0

    _ : S , w2 ⊨ And (var "p") (var "q")
    _ = proofAnd S w2 (var "p") (var "q") (proofvar S w2 "p" refl) (proofvar S w2 "q" refl)

    _ : S , w0 ⊨ Or (var "p") (var "q")
    _ = proofOr1 S w0 (var "p") (var "q") (proofvar S w0 "p" refl) 

    _ : S , w2 ⊨ ⋄ d (var "p")
    _ = proof⋄ S w2 (var "p") d w0 refl (proofvar S w0 "p" refl)

    --Lemat pomocniczy
    lemma : ∀ (t : World ) → Rel w1 d t ≡ tt → Val "q" t ≡ tt
    lemma w2 x = refl
 
    _ : S , w1 ⊨ □ d (var "q")
    _ = proof□ S w1 (var "q") d λ t x → proofvar S t "q" (lemma t x) 


--przykład nr 2
module ⊨-example2 where

    data World : Set where
        w0 : World
        w1 : World
        w2 : World
        w3 : World
        w4 : World

    Rel : World → D → World → 𝔹
    Rel w0 d w0 = ff
    Rel w0 d w1 = tt
    Rel w0 d w2 = tt
    Rel w0 d w3 = ff
    Rel w0 d w4 = ff 
    Rel w1 d w0 = ff
    Rel w1 d w1 = ff
    Rel w1 d w2 = tt
    Rel w1 d w3 = ff
    Rel w1 d w4 = ff
    Rel w2 d w0 = ff
    Rel w2 d w1 = ff 
    Rel w2 d w2 = ff 
    Rel w2 d w3 = ff 
    Rel w2 d w4 = ff
    Rel w3 d w0 = ff
    Rel w3 d w1 = ff
    Rel w3 d w2 = tt
    Rel w3 d w3 = ff
    Rel w3 d w4 = tt
    Rel w4 d w0 = tt
    Rel w4 d w1 = ff 
    Rel w4 d w2 = tt 
    Rel w4 d w3 = ff 
    Rel w4 d w4 = tt 

    Val : string → World → 𝔹 
    Val "p" w0 = tt 
    Val "q" w0 = ff
    Val "r" w0 = ff
    Val "p" w1 = ff 
    Val "q" w1 = tt
    Val "r" w1 = ff
    Val "p" w2 = tt 
    Val "q" w2 = tt
    Val "r" w2 = tt
    Val "p" w3 = ff 
    Val "q" w3 = tt
    Val "r" w3 = tt
    Val "p" w4 = tt 
    Val "q" w4 = ff
    Val "r" w4 = tt
    Val _ _ = ff

    S : struct
    S = record { W = World ; R = Rel ; V = Val }

    _ : S , w0 ⊨ Or (var "p") (var "q")
    _ = proofOr1 S w0 (var "p") (var "q")  (proofvar S w0 "p" refl)

    _ : S , w1 ⊨ And (⋄ d (var "q")) (var "q")
    _ = proofAnd S w1 (⋄ d (var "q")) (var "q") (proof⋄ S w1 (var "q") d w2 refl 
        (proofvar S w2 "q" refl)) (proofvar S w1 "q" refl)


    --Lemat pomocniczy
    lemma : ∀ (t : World ) → Rel w4 d t ≡ tt → Val "p" t ≡ tt
    lemma w0 x = refl
    lemma w2 x = refl
    lemma w4 x = refl

    _ : S , w4 ⊨ □ d (var "p")
    _ = proof□ S w4 (var "p") d λ t x → proofvar S t "p" (lemma t x)

    _ : S , w3 ⊨ Or ( And (var "p") (var "q") ) ( And (var "q") (var "r") )
    _ = proofOr2 S w3 (And (var "p") (var "q")) (And (var "q") (var "r")) (proofAnd S w3 (var "q") (var "r") (proofvar S w3 "q" refl) (proofvar S w3 "r" refl))
  