-- TODO: use Setoid
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; trans; cong; cong-app; sym; refl; _≢_; subst; module ≡-Reasoning) public
open import Relation.Nullary
open import Data.Empty
open import Agda.Primitive
open import Data.Unit
open import Algebra.Bundles renaming (Monoid to M)
open import Algebra.Core using (Op₂)
open import Algebra.Structures using (IsMonoid)

-- category without universe-poly

Arrow : {a b : Level} → Set a → Set b → (ℓ : Level) → Set (a ⊔ b ⊔ lsuc ℓ)
Arrow A B ℓ = A → B → Set ℓ

record Category (o ℓ : Level) : Set (lsuc o ⊔ lsuc ℓ) where
  infixr 9 _∘_
  field
    -- Objects
    Object : Set o
    -- Maps
    _⇒_ : Arrow Object Object ℓ
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

record isomorphism {o ℓ : Level} (c : Category o ℓ) (A B : Category.Object c) : Set ℓ where
  open Category c
  field
    to : (A ⇒ B)
    from : (B ⇒ A)
    id₁ : from ∘ to ≡ id
    id₂ : to ∘ from ≡ id

record isInverse {o ℓ : Level}
                 (c : Category o ℓ)
                 (A B : Category.Object c)
                 (f : (Category._⇒_) c A B)
                 (g : (Category._⇒_) c B A) : Set ℓ where
  open Category c
  field
    idA : g ∘ f ≡ id
    idB : f ∘ g ≡ id


module Exercise {o ℓ : Level} (c : Category o ℓ) where
  open Category c

  variable
    A : Object
    B : Object
    C : Object

  -- Exercise 1 (R) (page 41)
  -- ids are isomrophisms
  open isomorphism
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
          id₁ = lemma-id₁ AtoB BtoC CtoB BtoA idB' idA;
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
                  rewrite sym (law-assoc BtoC CtoB BtoA)
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
                  rewrite sym (law-assoc BtoA AtoB BtoC)
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

  -- Exercise 3 (a)
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
        step2 = sym (law-assoc h f g)
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

  -- Exercise 3 (b)
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
        step3 = trans step2 (sym (law-assoc g f k))
        step4 = sym (cong (h ∘_) idB)
        step5 = cong (k ∘_) idB
        step6 = trans (trans step4 step3) step5
        step7 = sym (law-id-r h)
        step8 = trans step7 step6
        step9 = trans step8 (law-id-r k)
     in step9

-- Exercise 3 (c)
-- Note that this proof is not within the Exercise module.
-- This is because the module is parametrized over a category c,
--  i.e., for all of our propositions defined inside the module, there's
--  a category c universally quantified (at the outermost scope).
--  Therefore we don't have to type out the category c and objects A B in c
--  in each type.
-- However, for exercise 3(c), the proposition we are proving is in the form of:
--  ¬ ∀ (c : Category) (A B : Object c) ...
-- which is equivalent to:
--  (∀ (c : Category) (A B : ...) .... ) → ⊥
-- Note that the universal quantifier ∀ is not at the outermost scope, therefore
--  it wouldn't work to define this proposition in the module.
--
-- Intuitively, we want to say "it is not for all category that ... is true"
--  or "There exists a category such that ... is NOT true"

-- Category SET
SET : Category _ _
SET =
  record {
        Object = Set;
        _⇒_ = λ A B → (A → B);
        id = λ x → x;
        _∘_ = λ g f x → g (f x);
        law-id-r = λ f → refl;
        law-id-l = λ f → refl;
        law-assoc = λ f g h → refl
  } where open Category

wrong-cancel-law : ¬ ((c : Category _ _)
                → let open Category c in
                   (A : Object)
                → (f : A ⇒ A)
                → (g : A ⇒ A)
                → isInverse c A A f g
                → (h : A ⇒ A)
                → (k : A ⇒ A)
                → (h ∘ f ≡ f ∘ k)
                → h ≡ k)
wrong-cancel-law prop =
  let c = prop SET Bool not not record { idA = notnot≡id ; idB = notnot≡id } (const true) (const false) refl
   in lemma2 c
   where
    open import Level
    open import Data.Bool
    open import Function using (const)
    open import Axiom.Extensionality.Propositional

    open Category SET

    lemma : true ≡ false → ⊥
    lemma ()

    lemma2 : const {B = Bool} true ≡ const {B = Bool} false → ⊥
    lemma2 eq = lemma (cong-app eq true)

    lemma3 : ∀ (b : Bool) → (not ∘ not) b ≡ (id b)
    lemma3 false = refl
    lemma3 true = refl

    postulate
      funext : {a b : Level} → Extensionality a b

    -- this proof requires function extensionality
    notnot≡id : not ∘ not ≡ id
    notnot≡id = funext lemma3

-- Speicializing the Monoid from stdlib to use propositional equality as their equivalance relation
-- This is purely because my poor encoding of Category
-- The real fix is to use setoid!!
record Monoid (c ℓ : Level) : Set (lsuc (c ⊔ ℓ)) where
  field
    Carrier : Set c
    _∙_      : Op₂ Carrier
    ε        : Carrier
    isMonoid : IsMonoid _≡_ _∙_ ε

  private
    repr = record { Carrier = Carrier ; _≈_ = _≡_ ; _∙_ = _∙_ ; ε = ε ; isMonoid = isMonoid }

  open M repr hiding (Carrier; _≈_;  _∙_; ε; isMonoid) public

-- A monoid is a category of a single object
MonoidCat : {c ℓ : Level} → Monoid c ℓ → Category lzero c
MonoidCat m = record
           { Object = ⊤
           ; _⇒_ = λ _ _ → Carrier
           ; id = λ {A} → ε
           ; _∘_ = _∙_
           ; law-id-r = identityʳ
           ; law-id-l = identityˡ
           ; law-assoc = λ f g h → PropEq.sym (assoc h g f)
           }
           where open Monoid m

