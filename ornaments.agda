open import Agda.Primitive

open import Agda.Builtin.Equality

record  One : Set where
  constructor <>

data Two : Set where
  ff tt : Two

--Descriptions of indexed types.
data Desc (I : Set) : Set₁ where
  arg : (A : Set) → (A → Desc I) → Desc I
  rec : I → Desc I → Desc I
  ret : I → Desc I

record Σ (A : Set) (f : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : f fst

NatDesc : Desc One
NatDesc = arg Two (λ { ff → ret <> ; tt → rec <> (ret <>)})

--Interpretation of descriptions (unfixed)
[_] : {I : Set} → Desc I → (I → Set) → I → Set
[ arg A D ] R i = Σ A (λ a → [ D a ] R i)
[ rec h D ] R i = Σ (R h) (λ _ → [ D ] R i)
[ ret o ] R i = o ≡ i

--Fixed point of Descs.
data Data {I : Set} (D : Desc I) :  I → Set where
  <_> : {i : I} → [ D ] (Data D) i → Data D i --Small typo here in Conor, he's applying Data D to I directly, rather than using i as an arg to [D] (Data D).

Nat : Set
Nat = Data NatDesc <>

zero : Nat
zero = < ff , refl >

suc : Nat → Nat
suc n = < tt , (n , refl) >

VecDesc : Set → Desc Nat
VecDesc A =
  arg Two (λ { ff → ret zero ; tt → arg A (λ _ → arg Nat (λ n → rec n (ret (suc n))))})

Vec : Set → Nat → Set
Vec A n = Data (VecDesc A) n

nil : {A : Set} → Vec A zero
nil {A} = < ff , refl >

cons : {n : Nat} {X : Set} → X → Vec X n → Vec X (suc n)
cons {n} {X} x xs = < tt , (x , (n , (xs , refl))) >

--Index-respecting functions
_⊂_ : {I : Set} → (I → Set) → (I → Set) → Set
_⊂_  {I} X Y  = (i : I) → X i → Y i

map : ∀ {I} {X Y} → (D : Desc I) → (X ⊂ Y) → [ D ] X ⊂ [ D ] Y
map (arg A D) f i (a , d) = a , map (D a) f i d
map (rec h D) f i (x , d) = f h x , map D f i d
map (ret o) f i x = x
