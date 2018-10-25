open import Agda.Builtin.Equality

--A dumping ground of basic machinery we need all the time.
record One : Set where
  constructor <>

record Σ (A : Set) (f : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : f fst

open Σ

data Two : Set where
  zz ss : Two --Terrible notation, chosen for compatibility with Conor.

cong : ∀ {l} {A B : Set l} → {x y : A} → (f : A → B) → (x ≡ y) → f x ≡ f y
cong _ refl = refl

--Inverse image of e.
data Inv { I J : Set} (e : J → I) : I → Set where
  inv : (j : J) → Inv e (e j)
