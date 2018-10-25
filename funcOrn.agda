open import Agda.Builtin.Equality
open import Basics

--Universe encoding for data types.
--This uses a similar indexed-set construction,
--but leaves off the constraints on indexes used by Conor.
--The idea is to introduce an exponentialised version later,
--which will (via pattern matching, essentially)
--avoid index constraints by generating the applicable constructors
--up front.
data IDesc (I : Set) : Set₁ where
  var : I → IDesc I
  unit : IDesc I
  Πd : (S : Set) → (S → IDesc I) → IDesc I
  Σd : (S : Set) → (S → IDesc I) → IDesc I

--Interpretation.
--Note that this doesn't have a way to constrain indexes,
--due to lacking the ret constructor of Conor's original
--universe.
[_] : ∀ {I} → IDesc I → (X : I → Set) → Set
[ var i ] X = X i
[ unit ] X = One
[ Πd S T ] X = (s : S) → [ T s ] X
[ Σd S T ] X = Σ S λ s → [ T s ] X

--With the above, we can define codes for (unfixed) functors indexed by One:
NatD : IDesc One
NatD = Σd Two λ { zz → unit ; ss → var <> }

func : Set → Set₁
func I = I → IDesc I

--The original paper overloads its notation heavily, I'll
--suffix as-needed.
[_]f : ∀ {I} → func I → (I → Set) → I → Set
[ D ]f X = λ i → [ D i ] X

--We have a generic map operator.
--First, we define index-respecting mappings.
_⊆_ : {I : Set} (X Y : I → Set) → Set
_⊆_ {I} X Y = (i : I) → X i → Y i

--To define map, we use this helper, which de-exponentialises
--the description.
--The definition makes intuitive sense:
--apply ϕ wherever you see a recursive node,
--otherwise leave the structure as-is.
mapIDesc : ∀ {I} {X Y : I → Set} (D : IDesc I) →
           (X ⊆ Y) → [ D ] X → [ D ] Y
mapIDesc (var i) ϕ x = ϕ i x
mapIDesc unit ϕ x = <>
mapIDesc (Πd S T) ϕ x = λ s → mapIDesc (T s) ϕ (x s)
mapIDesc (Σd S T) ϕ (s , t) = s , mapIDesc (T s) ϕ t

--Map just gets the actual description at index i,
--then maps across the resulting IDesc.
map : ∀ {I X Y} → (D : func I) → X ⊆ Y → [ D ]f X ⊆ [ D ]f Y
map D ϕ i x = mapIDesc (D i) ϕ x

--Fixed points
data μ {I : Set} (D : func I) (i : I) : Set where
  inj : ([ D ]f (μ D) i) → μ D i

--D-Algebras, which map a description with recursive nodes
--in the family X to an element of X at the same index.
Alg : ∀ {I} → func I → (I → Set) → Set
Alg D X = [ D ]f X ⊆ X

--An interesting question, not touched on in the paper,
--is whether this universe admits a generic catamorphism.
--It does.
--fold is made structurally recursive using the same mapFold
--trick as for Conor's original description type.

mapFold : ∀ {I X} → (D : IDesc I) → (E : func I) → Alg E X → [ D ] (μ E) → [ D ] X
fold : ∀ {I X} → (D : func I) → Alg D X → μ D ⊆ X

mapFold (var i) E ϕ x = fold E ϕ i x
mapFold unit E ϕ x = <>
mapFold (Πd S T) E ϕ x = λ s → mapFold (T s) E ϕ (x s)
mapFold (Σd S T) E ϕ (s , t) = s , mapFold (T s) E ϕ t

fold D ϕ i (inj x) = ϕ i (mapFold (D i) D ϕ x)

--Next: Can we define the induction principle referred to in
--Dagand & McBride?
--First thing we need is to define their 'P holds of subexpressions' type.
--This signature is terrifying, but basically, P is a property of the indexed family
--μ D, x is a value at some index, we want to declare evidence for each subexpression satisfying
--P at the appropriate index.

--As per usual, we need the mapFold-style trick.
allSubsI : {I : Set} (D : IDesc I) (E : func I) (P : (i : I) → μ E i → Set) (i : I) (x : [ D ] (μ E)) → Set
allSubs : {I : Set} (D : func I) (P : (i : I) → μ D i → Set) (i : I) (x : [ D ]f (μ D) i) → Set

allSubsI (var j) E P i x = P j x --Recursive subnode, so demand P.
allSubsI unit E P i x = One --No subnodes, so demand trivial evidence.
allSubsI (Πd S T) E P i x = (s : S) → allSubsI (T s) E P i (x s) --A function, so demand evidence ∀ args.
allSubsI (Σd S T) E P i (s , t) = allSubsI (T s) E P i t --Existential, there's some s such that we have a t. The s has no subnodes, so only demand of t.

allSubs D P i x = allSubsI (D i) D P i x

--Induction follows the same pattern as the generic catamorphism above.
--Effectively, we're constructing proof that the property holds in all subtrees
--(in inductionLoop), then applying the induction principle to the proof created.
induction : ∀ {I} D → (P : (i : I) → μ D i → Set) → ((i : I) → (x : [ D ]f (μ D) i) → allSubs D P i x → P i (inj x)) → (i : I) → (x : μ D i) → P i x
inductionLoop : ∀ {I} (D : IDesc I) E (P : (i : I) → μ E i → Set) → ((i : I) (x : [ E ]f (μ E) i) → allSubs E P i x → P i (inj x)) → (i : I) (x : [ D ] (μ E)) → allSubsI D E P i x

inductionLoop (var j) E P α i x = induction E P α j x
inductionLoop unit E P α i x = <>
inductionLoop (Πd S T) E P α i x = λ s → inductionLoop(T s) E P α i (x s)
inductionLoop (Σd S T) E P α i (s , t) = inductionLoop (T s) E P α i t

induction D P α i (inj x) = α i x (inductionLoop (D i) D P α i x)

--To make this all a bit less abstract, can we define Nats?
NatFunc : func One
NatFunc = λ _ → NatD

Nat : Set
Nat = μ NatFunc <>

--Some constructors to make life easier
--TODO: Use pattern synonyms so we can use these on the left-hand side as well.
zero : Nat
zero = inj (zz , <>)

suc : Nat → Nat
suc n = inj (ss , n)

adda : Nat → Alg NatFunc (λ _ → Nat)
adda n <> (zz , <>) = n
adda n <> (ss , sum) = suc sum

--Addition by way of a generic fold:
_+Nat_ : Nat → Nat → Nat
x +Nat y = fold NatFunc (adda y) <> x

--Some unit tests:
1+Nat0=1 : (suc zero +Nat zero) ≡ suc zero
1+Nat0=1 = refl

0+Nat1=1 : (zero +Nat suc zero) ≡ suc zero
0+Nat1=1 = refl

1+Nat1=2 : (suc zero +Nat suc zero) ≡ suc (suc zero)
1+Nat1=2 = refl

--Ok, that seems to define what we want.
--Next, can we show basic properties by induction?
n+Nat0=n : (n : Nat) → (n +Nat zero) ≡ n
n+Nat0=n = induction NatFunc (λ _ n → (n +Nat zero) ≡ n) (λ _ → step) <>
  where
    step : (x : [ NatFunc ]f (μ NatFunc) <>) → allSubs NatFunc (λ _ n → (n +Nat zero) ≡ n) <> x → (inj x +Nat zero) ≡ inj x
    --Usage is actually not too terrifying, surprisingly.
    step (zz , <>) rec = refl --The zero case.
    step (ss , n) rec = cong suc rec

m+Natsucn=sucm+Natn : (m n : Nat) → (m +Nat (suc n)) ≡ suc (m +Nat n)
m+Natsucn=sucm+Natn m n = induction NatFunc (λ _ m → (m +Nat (suc n)) ≡ suc (m +Nat n)) (λ _ → step) <> m
  where
    step : (x : [ NatFunc ]f (μ NatFunc) <>) → allSubs NatFunc (λ _ m → (m +Nat (suc n)) ≡ suc (m +Nat n)) <> x → ((inj x) +Nat suc n) ≡ suc (inj x +Nat n)
    step (zz , <>) rec = refl
    step (ss , snd) rec rewrite rec = refl

+Nat-comm : (m n : Nat) → (m +Nat n) ≡ (n +Nat m)
+Nat-comm m = induction NatFunc (λ _ n → (m +Nat n) ≡ (n +Nat m)) (λ _ → step) <>
  where
    step : (x : [ NatFunc ]f (μ NatFunc) <>) → allSubs NatFunc (λ _ n → (m +Nat n) ≡ (n +Nat m)) <> x → (m +Nat (inj x)) ≡ ((inj x) +Nat m)
    step (zz , <>) rec = n+Nat0=n m
    step (ss , n) rec rewrite m+Natsucn=sucm+Natn m n = cong suc rec

--Wew, ok, that's a convincing enough demonstration that this induction principle works.

--Ornaments.
--These are similar to Conor's original, the main difference
--is the introduction of delete.
--Following Dagand, I'll rename new to insert.
data Orn {I K : Set} (u : I → K) : (D : IDesc K) →  Set₁ where
  insert : ∀ {D} (S : Set) → (S → Orn u D) → Orn u D
  var : {k : K} → Inv u k → Orn u (var k)
  unit : Orn u unit
  Πo : ∀ {S} {T : S → IDesc K} → ((s : S) → Orn u (T s)) → Orn u (Πd S T)
  Σo : ∀ {S} {T : S → IDesc K} → ((s : S) → Orn u (T s)) → Orn u (Σd S T)
  delete : ∀ {S} {T : S → IDesc K} → (s : S) → Orn u (T s) → Orn u (Σd S T)

--Interpretation of ornaments.
[_]uo : ∀ {I K D} {u : I → K} → Orn u D → IDesc I
[ insert S T ]uo = Σd S λ s → [ T s ]uo
[ var (inv j) ]uo = var j
[ unit ]uo = unit
[ Πo x ]uo = Πd _ λ s → [ x s ]uo
[ Σo x ]uo = Σd _ λ s → [ x s ]uo
[ delete s O ]uo = [ O ]uo

--Exponentiated ornaments
orn : {I K : Set} (u : I → K) (D : func K) → Set₁
orn {I} u D = (i : I) → Orn u (D (u i))

--Interpretation of the above.
[_,_]o : { I K : Set} (D : func K) {u : I → K} (O : orn u D) → func I
[ D , O ]o = λ i → [ O i ]uo

--Finger exercise 1: Ornamenting Nat into list.
ListOrn : Set → orn {I = One} (λ _ → <>) NatFunc
ListOrn X <> = Σo λ { zz → unit ; ss → insert X λ _ → var (inv <>)}

ListFunc : Set → func One
ListFunc X = [ NatFunc , ListOrn X ]o

List : Set → Set
List X = μ (ListFunc X) <>

--Next step, Vects from lists:
VectOrn : (X : Set) → orn { I = Nat } (λ _ → <>) (ListFunc X)
VectOrn X (inj (zz , <>)) = delete zz unit --In the zz case, we ONLY offer the nil constructor. Delete allows us to eliminate the other one.
VectOrn X (inj (ss , n)) = delete ss (Σo λ _ → var (inv n)) --In the ss case, we only offer cons. We then further require the recursive index to be n.

--The interpretation of VectOrn looks sane, but let's build some constructors to be sure.
Vect : Set → Nat → Set
Vect X = μ ([ [ NatFunc , ListOrn X ]o , VectOrn X ]o)

--These look sane, and nicer than ornaments.agda's version.
nilV : ∀ {X} → Vect X zero
nilV = inj <>

consV : ∀ {X n} → X → Vect X n → Vect X (suc n)
consV x xs = inj (x , xs)

--As with Conor's original ornaments, these also have a forgetful mapping

forgetNTO : {I K : Set} →  {X : K → Set} {D : IDesc K} {u : I → K} (O : Orn u D) → [ [ O ]uo ] (λ i → (X (u i))) → [ D ] X
forgetNTO (insert S T) (s , t) = forgetNTO (T s) t
forgetNTO (var (inv j)) xs = xs
forgetNTO unit xs = <>
forgetNTO (Πo T) xs = λ s → forgetNTO (T s) (xs s)
forgetNTO (Σo T) (s , t) = s , forgetNTO (T s) t
forgetNTO (delete s O) xs = s , forgetNTO O xs

forgetNT : {I K : Set} {u : I → K } {D : func K} {X : K → Set} → {i : I} → (o : orn u D) → [ [ D , o ]o  ]f (λ i → (X (u i))) i → [ D ]f X (u i)
forgetNT {i = i} o x = forgetNTO (o i) x

forgetAlg : {I K : Set} {u : I → K} {D : func K} (o : orn u D) (i : I) → [ [ D , o ]o ]f (λ i → μ D (u i)) i → μ D (u i)
forgetAlg {D = D} o i x = inj (forgetNT {D = D} {X = μ D} o x)

forget : {I K : Set} {u : I → K} {D : func K} (o : orn u D) → μ [ D , o ]o  ⊆ λ i → μ D (u i)
forget o = fold _ (forgetAlg o)

nilL : {X : Set} → List X
nilL = inj (zz , <>)

consL : {X : Set} → X → List X → List X
consL x xs = inj (ss , (x , xs))

length : {X : Set} → List X → Nat
length {X} = forget (ListOrn X) <>
