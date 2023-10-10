open import Relation.Binary.PropositionalEquality
open import Data.Product

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
    law-assoc-sym : ∀ {A B C D : Object} → (f : A ⇒ B) → (g : B ⇒ C) → (h : C ⇒ D)
                → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)


record Isomorphism (c : Category) (A B : Category.Object c) : Set where
  open Category c
  field
    to : (A ⇒ B)
    from : (B ⇒ A)
    id₁ : from ∘ to ≡ id
    id₂ : to ∘ from ≡ id


module Exercise (c : Category) where
  open Category c

  variable
    A : Object
    B : Object
    C : Object

  -- Exercise 1 (R) (page 41)
  -- ids are isomrophisms
  iso-refl : Isomorphism c A A
  iso-refl =
    record {
      to =  id;
      from = id;
      id₁ = law-id-l id;
      id₂ = law-id-l id
    }

  -- Exercise 1 (S) (page 41)
  -- isomrophisms are symmetric
  iso-sym : Isomorphism c A B → Isomorphism c B A
  iso-sym record { to = to ; from = from ; id₁ = id₁ ; id₂ = id₂ } =
    record {
      to = from;
      from = to;
      id₁ = id₂;
      id₂ = id₁
    }

  -- Exercise 1 (T) (page 41)
  -- isomrophisms are transitive
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

  iso-trans : Isomorphism c A B → Isomorphism c B C → Isomorphism c A C
  iso-trans record { to = AtoB ; from = BtoA ; id₁ = idA ; id₂ = idB } -- isomorphism from A to B
            record { to = BtoC ; from = CtoB ; id₁ = idB' ; id₂ = idC } -- isomorphism from B to C
            rewrite law-assoc AtoB BtoC (BtoA ∘ CtoB)
      = record {
          to = BtoC ∘ AtoB;
          from = BtoA ∘ CtoB;
          id₁ =  lemma-id₁ AtoB BtoC CtoB BtoA idB' idA;
          id₂ =  lemma-id₂ AtoB BtoC CtoB BtoA idC idB
        }










