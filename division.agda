open import Category as C using (Category; _≡_)
open import Data.Product using (∃-syntax; _,_)

-- Page 45 - Page 54
module Division (c : Category) where

open C
open Category c

private
  variable
    A : Object
    B : Object
    C : Object

record Determination (f : A ⇒ B) (h : A ⇒ C) : Set where
  field
    det : B ⇒ C
    isDeterminaton : h ≡ det ∘ f

record Choice (g : B ⇒ C) (h : A ⇒ C) : Set where
  field
    choice : A ⇒ B
    isChoice : h ≡ g ∘ choice

-- Retraction is a special Determination problem
Retraction : (f : A ⇒ B) → Set
Retraction f = Determination f id

-- Section is a special Choice problem
Section : (f : A ⇒ B) → Set
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
Monomorphism : (f : A ⇒ B) → Set₁
Monomorphism {A} {B} f =  (T : Object) → (x1 x2 : T ⇒ A) → f ∘ x1 ≡ f ∘ x2 → x1 ≡ x2

-- If morphism is function
-- then Epimorhism is the same as surjectivity
-- But note that surjectivity is not defined this way!!
Epimorphism : (f : A ⇒ B) → Set₁
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

Idempotent : (e : A ⇒ A) → Set
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

-- TODO: Compare the two definitions relevant to surjectivity
