open import Category as C using (Category; _≡_)
open import Data.Product using (∃-syntax; _,_)
open import Agda.Primitive

-- Page 45 - Page 54
module Division {o ℓ : Level} (c : Category o ℓ) where

open C
open Category c

private
  variable
    A : Object
    B : Object
    C : Object

record Determination (f : A ⇒ B) (h : A ⇒ C) : Set ℓ where
  field
    det : B ⇒ C
    isDeterminaton : h ≡ det ∘ f

record Choice (g : B ⇒ C) (h : A ⇒ C) : Set ℓ where
  field
    choice : A ⇒ B
    isChoice : h ≡ g ∘ choice

-- Retraction is a special Determination problem
Retraction : (f : A ⇒ B) → Set ℓ
Retraction f = Determination f id

-- Section is a special Choice problem
Section : (f : A ⇒ B) → Set ℓ
Section f = Choice f id

Proposition1 : (f : A ⇒ B) → Section f → (T : Object) → (y : T ⇒ B) → ∃[ x ] (f ∘ x ≡ y)
Proposition1 f record { choice = s ; isChoice = pf } T y = s ∘ y , lemma f s y (sym pf)
  where
    lemma : (f : A ⇒ B) → (s : B ⇒ A) → (y : T ⇒ B) → (f ∘ s ≡ id) → f ∘ s ∘ y ≡ y
    lemma f s y pf
      rewrite law-assoc y s f
      rewrite pf
      rewrite law-id-l y
      = refl

-- Exericise 6
Proposition1* : (f : A ⇒ B) → Retraction f → (T : Object) → (g : A ⇒ T) → ∃[ t ] t ∘ f ≡ g
Proposition1* f record { det = r ; isDeterminaton = pf } T g =  g ∘ r , lemma
  where
    lemma : (g ∘ r) ∘ f ≡ g
    lemma
      rewrite sym (law-assoc f r g)
      rewrite sym pf
      rewrite law-id-r g
      = refl

-- If morphism is function
-- then Monomorphism is the same as injectivity
Monomorphism : (f : A ⇒ B) → Set (o ⊔ ℓ)
Monomorphism {A} {B} f =  (T : Object) → (x1 x2 : T ⇒ A) → f ∘ x1 ≡ f ∘ x2 → x1 ≡ x2

-- If morphism is function
-- then Epimorhism is the same as surjectivity
-- But note that surjectivity is not defined this way!!
Epimorphism : (f : A ⇒ B) → Set (o ⊔ ℓ)
Epimorphism {A} {B} f = (T : Object) → (t1 t2 : B ⇒ T) → t1 ∘ f ≡ t2 ∘ f → t1 ≡ t2

-- If f has a retraction, then f must be a monomorphism
Proposition2 : (f : A ⇒ B)
             → Retraction f
             → Monomorphism f
             -- → (T : Object)
             -- → (x1 x2 : T ⇒ A)
             -- → f ∘ x1 ≡ f ∘ x2
             -- → x1 ≡ x2
Proposition2 f record { det = r ; isDeterminaton = pf } T x1 x2 fx1≡fx2 = begin
  x1           ≡⟨ sym (law-id-l x1) ⟩
  id ∘ x1      ≡⟨ cong (_∘ x1) pf ⟩
  (r ∘ f) ∘ x1 ≡⟨ sym (law-assoc x1 f r) ⟩
  r ∘ f ∘ x1   ≡⟨ cong (r ∘_) fx1≡fx2 ⟩
  r ∘ f ∘ x2   ≡⟨ (law-assoc x2 f r) ⟩
  (r ∘ f) ∘ x2 ≡⟨ sym (cong (_∘ x2) pf) ⟩
  id ∘ x2      ≡⟨ law-id-l x2 ⟩
  x2 ∎
  where open ≡-Reasoning


-- Exercise 7
-- If f has a section then f must be a epimorphism
Proposition2* : (f : A ⇒ B)
              → Section f
              → Epimorphism f
              -- → (T : Object)
              -- → (t1 t2 : B ⇒ T)
              -- → t1 ∘ f ≡ t2 ∘ f
              -- → t1 ≡ t2
Proposition2* f record { choice = s ; isChoice = pf } T t1 t2 t1f≡t2f = begin
  t1           ≡⟨ sym (law-id-r t1) ⟩
  t1 ∘ id      ≡⟨ cong (t1 ∘_) pf ⟩
  t1 ∘ f ∘ s   ≡⟨ law-assoc s f t1 ⟩
  (t1 ∘ f) ∘ s ≡⟨ cong (_∘ s) t1f≡t2f ⟩
  (t2 ∘ f) ∘ s ≡⟨ sym (law-assoc s f t2) ⟩
  t2 ∘ f ∘ s   ≡⟨ sym (cong (t2 ∘_) pf) ⟩
  t2 ∘ id      ≡⟨ law-id-r t2 ⟩
  t2 ∎
  where open ≡-Reasoning

Proposition3 : (f : A ⇒ B) → Retraction f → (g : B ⇒ C) → Retraction g → Retraction (g ∘ f)
Proposition3 f record { det = r1 ; isDeterminaton = pf1 } g record { det = r2 ; isDeterminaton = pf2 } =
  record {
    det = r1 ∘ r2 ;
    isDeterminaton = lemma
  }
  where
    lemma : id ≡ (r1 ∘ r2) ∘ g ∘ f
    lemma
      rewrite law-assoc f g (r1 ∘ r2)
      rewrite sym (law-assoc g r2 r1)
      rewrite sym pf2
      rewrite law-id-r r1
      rewrite sym pf1
      = refl

-- Exercise 8
Proposition3* : (f : A ⇒ B) → Section f → (g : B ⇒ C) → Section g → Section (g ∘ f)
Proposition3* f record { choice = s1 ; isChoice = pf1 } g record { choice = s2 ; isChoice = pf2 } =
  record {
    choice =  s1 ∘ s2 ;
    isChoice = lemma
  }
  where
    lemma : id ≡ (g ∘ f) ∘ s1 ∘ s2
    lemma
      rewrite law-assoc s2 s1 (g ∘ f)
      rewrite sym (law-assoc s1 f g)
      rewrite sym pf1
      rewrite law-id-r g
      rewrite sym pf2
      = refl

Idempotent : (e : A ⇒ A) → Set ℓ
Idempotent e = e ∘ e ≡ e

Exercise9 : (f : A ⇒ B) → (r : B ⇒ A) → let e = r ∘ f in id ≡ e → Idempotent e
Exercise9 f r pf = lemma
  where
    lemma : (r ∘ f) ∘ r ∘ f ≡ r ∘ f
    lemma
      rewrite law-assoc f r (r ∘ f)
      rewrite sym pf
      rewrite law-id-l r
      = sym pf

-- TODO: the equational reasonsing steps can be simplified
uniqueness-of-inv : (f : A ⇒ B)
                  → (ret : Retraction f)
                  → (sec : Section f)
                  → let r = Determination.det ret;
                         s = Choice.choice sec
                      in r ≡ s
uniqueness-of-inv f
                  record { det = r ; isDeterminaton = pfret }
                  record { choice = s ; isChoice = pfsec }
                  = begin
                  r           ≡⟨ sym (law-id-r r) ⟩
                  r ∘ id      ≡⟨ cong (r ∘_) pfsec ⟩
                  r ∘ f ∘ s   ≡⟨ law-assoc s f r ⟩
                  (r ∘ f) ∘ s ≡⟨ sym (cong (_∘ s) pfret) ⟩
                  id ∘ s      ≡⟨ law-id-l s ⟩
                  s ∎
                  where open ≡-Reasoning

module Surjectivity where
  -- In page 52, monomorphism is defined in terms of "being injective for maps from T"
  -- i.e., forall Object T, given any pair of maps x1, x2 : T ⇒ A, if f ∘ x1 = f ∘ x2, then x1 = x2.
  -- we way f is a monomorphism or f is injective.
  --
  -- However, weirdly, Epimorphism is not defined using surjectivity.
  -- The definition below (which is the dual of the definition for monomorphism) defines epimorphism.
  -- But we don't say "f is surjective".
  Epi : (f : A ⇒ B) → Set (o ⊔ ℓ)
  Epi {A} {B} f = (T : Object) → (t1 t2 : B ⇒ T) → t1 ∘ f ≡ t2 ∘ f → t1 ≡ t2

  -- In fact, on page 51, the book gives an informal definition for what it means to be "surjective"
  -- Which is similar to the type of proposition1 (except that in prop1 we assume f has a section)
  surjectiveFromT : (f : A ⇒ B) → (T : Object) → Set ℓ
  surjectiveFromT {A} {B} f T = (y : T ⇒ B) → ∃[ x ] (f ∘ x ≡ y)

  -- Then I guess surjectivity can be defined below
  surjective : (f : A ⇒ B) → Set (o ⊔ ℓ)
  surjective {A} {B} f = (T : Object) → (y : T ⇒ B) → ∃[ x ] (f ∘ x ≡ y)

  -- Now naturally, we shall ask, are the two definition, namely `Epi` and `surjective` eqivalent?
  surjective⇒epi : (f : A ⇒ B) → surjective f → Epi f
  surjective⇒epi f fsurj = epi
    where
      epi : Epi f
      epi T t1 t2 t1f≡t2f = {!!}

  epi⇒surjective : (f : A ⇒ B) → Epi f → surjective f
  epi⇒surjective f fepi = fsurj
    where
      fsurj : surjective f
      fsurj T y = {!!}, {!!}

  -- TODO: select T to be B
  surjective⇒section : (f : A ⇒ B) → surjective f → Section f
  surjective⇒section f fsuj = {!!}

  -- It doesn't seem possible to prove either direction.
  -- Therefore we should consider the definition of epimorphism and surjectivity irrelevant.
  --
  -- To see why epimorphism does not imply surjectivity, we can think about the category of monoids (Mon)
  -- In Mon, the morphisms are homomorphisms (structure preserving maps) between monoids
  -- Now, we define our f to be a inclusion map ι : ℕ → ℤ defined as {0 -> 0, 1 -> 1 ....},
  -- which is clearly non-surjective (the negative half of ℤ are not mapped).
  --
  -- Then let's prove for two homomorphisms t1 and t2 from ℤ to arbitrary monoid (M, ×, idM),
  -- if t1 ∘ ι ≡ t2 ∘ ι, then t1 ≡ t2.
  -- We prove by contradiction, thus we suppose t1 ≠ t2.
  -- That means there exists some n ∈ ℤ, where t1(n) ≠ t2(n)
  -- recall a homomorphism h : M → N between two monoids (M, *) (N, ∘) requires:
  -- h(x * y) = h(x) ∘ h(y) for all x, y ∈ M
  -- and h(eM) = eN where eM and eN are identity elements for M and N.
  -- (in our case, the operators for both ℕ and ℤ are both + and the identity elements are 0).
  -- Since t1 t2 are homomorphisms, that means we have
  -- t1(n + -n) ≡ t1(0) ≡ idM ≡ t1(n) × t1(-n) and
  -- t2(n + -n) ≡ t2(0) ≡ idM ≡ t2(n) × t2(-n)
  -- since t1(n) ≠ t2(n), and the inverse in a group is unique, we got t1(-n) ≠ t2(-n)
  -- (homomorphism of monoids preserves group structure, so M must also be a group)
  --
  -- Now the interesting thing is, one of n and -n must be in ℕ
  -- but we already assumed t1 ∘ f ≡ t2 ∘ f
  -- then for f(x) = n or -n (whichever is ℕ), we have (t1 ∘ f) x ≠ (t2 ∘ f) x,
  -- hense t1 ∘ f ≠ t2 ∘ f, which contradicts our assumption.
  --
  -- Therefore, we proved that if t1 ∘ f ≡ t2 ∘ f, then t1 ≡ t2.
  -- Therefore, f is an epimorphism, but clearly f is not surjective.


  -- Now let's have an example in SET
  -- still consider the function ι above
  -- We already know it's not surjective.
  -- For epimorphism: if t1 ∘ ι ≡ t2 ∘ ι, can we prove t1 ≡ t2.
  -- Well, since now t1 and t2 can be arbitrary functions, this is clearly false
  -- we can have t1 and t2 defined differently on the negative integers,
  -- while having the same definition on the positives.
  -- (in other words, we only need t1 and t2 to be the same on the image of ι).

  -- Intuitively, the difference between Mon aand SET are due to homomorphism requires
  -- more structure preserving, thus disallow arbitrary functions to qualify as morphisms
  -- in the category.
  --
  -- To sum up, surjectivity and epimorphism coincide in many categories, but they are not always the same.
  -- Their definitions are also separate and distinct.

