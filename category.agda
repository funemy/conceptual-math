open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Empty

-- category without universe-poly

Arrow : Set → Set →  Set₁
Arrow A B = A → B → Set

record Category : Set₁ where
  infixr 9 _∘_
  field
    -- Objects
    Object : Set
    -- Maps
    _⇒_ : Arrow Object Object
    -- Identity Maps
    id : ∀ {A : Object} → A ⇒ A
    -- Composite Maps
    _∘_ : ∀ {A B C : Object} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)
    -- rules
    -- identity laws
    law-id-r : ∀ {A B : Object} → (f : A ⇒ B) → f ∘ id ≡ f
    law-id-l : ∀ {A B : Object} → (f : A ⇒ B) → id ∘ f ≡ f
    -- associative law
    law-assoc : ∀ {A B C D : Object} → (f : A ⇒ B) → (g : B ⇒ C) → (h : C ⇒ D)
                → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
    -- the associative law is symmetric
    -- this law is purely for doing proofs in agda
    law-assoc-sym : ∀ {A B C D : Object} → (f : A ⇒ B) → (g : B ⇒ C) → (h : C ⇒ D)
                → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)


record isomorphism (c : Category) (A B : Category.Object c) : Set where
  open Category c
  field
    to : (A ⇒ B)
    from : (B ⇒ A)
    id₁ : from ∘ to ≡ id
    id₂ : to ∘ from ≡ id

-- TODO: agda question, isomorphism and isInverse are not the same definition right?
record isInverse (c : Category)
                 (A B : Category.Object c)
                 (f : (Category._⇒_) c A B)
                 (g : (Category._⇒_) c B A) : Set₁ where
  open Category c
  field
    idA : g ∘ f ≡ id
    idB : f ∘ g ≡ id


module Exercise (c : Category) where
  open Category c

  variable
    A : Object
    B : Object
    C : Object

  -- Exercise 1 (R) (page 41)
  -- ids are isomrophisms
  iso-refl : isomorphism c A A
  iso-refl =
    record {
      to =  id;
      from = id;
      id₁ = law-id-l id;
      id₂ = law-id-l id
    }

  -- Exercise 1 (S) (page 41)
  -- isomrophisms are symmetric
  iso-sym : isomorphism c A B → isomorphism c B A
  iso-sym record { to = to ; from = from ; id₁ = id₁ ; id₂ = id₂ } =
    record {
      to = from;
      from = to;
      id₁ = id₂;
      id₂ = id₁
    }

  -- Exercise 1 (T) (page 41)
  -- isomrophisms are transitive

  iso-trans : isomorphism c A B → isomorphism c B C → isomorphism c A C
  iso-trans record { to = AtoB ; from = BtoA ; id₁ = idA ; id₂ = idB } -- isomorphism from A to B
            record { to = BtoC ; from = CtoB ; id₁ = idB' ; id₂ = idC } -- isomorphism from B to C
            rewrite law-assoc AtoB BtoC (BtoA ∘ CtoB)
      = record {
          to = BtoC ∘ AtoB;
          from = BtoA ∘ CtoB;
          id₁ =  lemma-id₁ AtoB BtoC CtoB BtoA idB' idA;
          id₂ =  lemma-id₂ AtoB BtoC CtoB BtoA idC idB
        }
        where
        lemma-id₁ : (AtoB : A ⇒ B)
              → (BtoC : B ⇒ C)
              → (CtoB : C ⇒ B)
              → (BtoA : B ⇒ A)
              → (idB' : CtoB ∘ BtoC ≡ id)
              → (idA : BtoA ∘ AtoB ≡ id)
              → (BtoA ∘ CtoB) ∘ BtoC ∘ AtoB ≡ id
        lemma-id₁ AtoB BtoC CtoB BtoA idB' idA
                  rewrite law-assoc AtoB BtoC (BtoA ∘ CtoB)
                  rewrite law-assoc-sym BtoC CtoB BtoA
                  rewrite idB'
                  rewrite law-id-r BtoA
                  rewrite idA
                  = refl

        lemma-id₂ :  (AtoB : A ⇒ B)
              → (BtoC : B ⇒ C)
              → (CtoB : C ⇒ B)
              → (BtoA : B ⇒ A)
              → (idC : BtoC ∘ CtoB ≡ id)
              → (idB : AtoB ∘ BtoA ≡ id)
              → (BtoC ∘ AtoB) ∘ BtoA ∘ CtoB ≡ id
        lemma-id₂ AtoB BtoC CtoB BtoA idC idB
                  rewrite law-assoc CtoB BtoA (BtoC ∘ AtoB)
                  rewrite law-assoc-sym BtoA AtoB BtoC
                  rewrite idB
                  rewrite law-id-r BtoC
                  rewrite idC
                  = refl

  -- Exercise 2
  -- If a morphism has an inverse, then this inverse is unique
  -- Equivalently, any two inverses of the same morphism are equal
  unique-inverse : (f : A ⇒ B)
                   → (g : B ⇒ A)
                   → (k : B ⇒ A)
                   → isInverse c A B f g
                   → isInverse c A B f k
                   → g ≡ k
  unique-inverse f g k
                 record { idA = idA ; idB = idB } -- g is an inverse of f
                 record { idA = idA' ; idB = idB' } -- k is an inverse of f
                 =
                 let step1 = cong (k ∘_) idB
                     step2 = (law-assoc g f k)
                     step3 = sym step2
                     step4 = trans step3 step1
                     step5 = cong (_∘ g) idA'
                     step6 = sym step5
                     step7 = trans step6 step4
                     step8 = trans (sym (law-id-l g)) step7
                     step9 = trans step8 (law-id-r k)
                  in step9

  -- Exercise 3
  -- If f has an inverse, then f satisfies two cancellation laws
  law-cancel-r : (f : B ⇒ C)
                 → (g : C ⇒ B)
                 → isInverse c B C f g
                 → (h : A ⇒ B)
                 → (k : A ⇒ B)
                 → (f ∘ h ≡ f ∘ k)
                 → h ≡ k
  law-cancel-r f g record { idA = idA ; idB = idB } h k fh≡fk =
    let step1 = cong (g ∘_) fh≡fk
        step2 = law-assoc-sym h f g
        step3 = trans step2 step1
        step4 = law-assoc k f g
        step5 = trans step3 step4
        step6 = sym (cong (_∘ h) idA)
        step7 = trans step6 step5
        step8 = (cong (_∘ k) idA)
        step9 = trans step7 step8
        step10 = trans (sym (law-id-l h)) step9
        step11 = trans step10 (law-id-l k)
      in step11

  law-cancel-l : (f : A ⇒ B)
                 → (g : B ⇒ A)
                 → isInverse c A B f g
                 → (h : B ⇒ C)
                 → (k : B ⇒ C)
                 → (h ∘ f ≡ k ∘ f)
                 → h ≡ k
  law-cancel-l f g record { idA = idA ; idB = idB } h k hf≡kf =
    let step1 = cong (_∘ g) hf≡kf
        step2 = trans (law-assoc g f h) step1
        step3 = trans step2 (law-assoc-sym g f k)
        step4 = sym (cong (h ∘_) idB)
        step5 = cong (k ∘_) idB
        step6 = trans (trans step4 step3) step5
        step7 = sym (law-id-r h)
        step8 = trans step7 step6
        step9 = trans step8 (law-id-r k)
     in step9

