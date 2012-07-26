import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PE hiding ([_])

module kv
  (K V : Set)
  {_<_ : Rel K Level.zero}
  (keyOrder : IsStrictTotalOrder _≡_ _<_)
where

open import Data.Unit using (⊤ ; tt)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Function using (_∘_)
open import Data.List hiding ([_])
open import Data.Product
open import Data.Sum
open import Data.Maybe
open import Relation.Nullary

x≤y→¬y<x : {A : Set} (_<_ : Rel A Level.zero) (ord : IsStrictPartialOrder _≡_ _<_) → ∀ {x y} → x < y ⊎ x ≡ y → ¬ y < x
x≤y→¬y<x _<_ ord = proof
  where
    module PO = IsStrictPartialOrder ord

    proof : ∀ {x y} → x < y ⊎ x ≡ y → ¬ y < x
    proof (inj₁ x<y) = λ y<x → PO.irrefl refl (PO.trans x<y y<x)
    proof (inj₂ x≡y) = PO.irrefl (sym x≡y)

data K+ : Set where
  [_] : K → K+
  ⊤ᴷ : K+

unbox-K+-equality : {x y : K} → [ x ] ≡ [ y ] → x ≡ y
unbox-K+-equality refl = refl

data _<+_ : Rel K+ Level.zero where
  [_]<⊤ : (k : K) → [ k ] <+ ⊤ᴷ
  <+[_] : {i j : K} → i < j → [ i ] <+ [ j ]

unbox-<+ : {x y : K} → [ x ] <+ [ y ] → x < y
unbox-<+ <+[ p₁ ] = p₁

module S = IsStrictTotalOrder keyOrder

SO : StrictTotalOrder _ _ _
SO = record { Carrier = K; _≈_ = _≡_; _<_ = _<_; isStrictTotalOrder = keyOrder }

k+Order : IsStrictTotalOrder _≡_ _<+_
k+Order = record { isEquivalence = isEquivalence; trans = trans+; compare = compare+; <-resp-≈ = resp₂ _ }
  where
    trans+ : Transitive _<+_
    trans+ [ k₁ ]<⊤ ()
    trans+ (<+[_] p) [ _ ]<⊤ = [ _ ]<⊤
    trans+ <+[ p ] <+[ q ] = <+[ S.trans p q ]

    compare+ : Trichotomous _≡_ _<+_
    compare+ [ x ] ⊤ᴷ = tri< [ x ]<⊤ (λ ()) (λ ())
    compare+ ⊤ᴷ [ x ] = tri> (λ ()) (λ ()) [ x ]<⊤
    compare+ ⊤ᴷ ⊤ᴷ = tri≈ (λ ()) refl (λ ())
    compare+ [ x ] [ y ] with S.compare x y
    compare+ [ x ] [ y ] | tri< a ¬b ¬c = tri< <+[ a ] (¬b ∘ unbox-K+-equality) (¬c ∘ unbox-<+)
    compare+ [ x ] [ y ] | tri≈ ¬a b ¬c = tri≈ (¬a ∘ unbox-<+) (cong [_] b) (¬c ∘ unbox-<+)
    compare+ [ x ] [ y ] | tri> ¬a ¬b c = tri> (¬a ∘ unbox-<+) (¬b ∘ unbox-K+-equality) <+[ c ]

module S+ = IsStrictTotalOrder k+Order

S+O : StrictTotalOrder _ _ _
S+O = record { Carrier = K+; _≈_ = _≡_; _<_ = _<+_; isStrictTotalOrder = k+Order }

<+⇒compare : ∀ {x y} → x <+ y → ∃ λ a → ∃ λ ¬b → ∃ λ ¬c → S+.compare x y ≡ tri< a ¬b ¬c
<+⇒compare {x} {y} p with S+.compare x y
<+⇒compare p | tri< a ¬b ¬c = a , ¬b , ¬c , refl
<+⇒compare p | tri≈ ¬a b ¬c = ⊥-elim (¬a p)
<+⇒compare p | tri> ¬a ¬b c = ⊥-elim (¬a p)

_≤+_ : Rel K+ Level.zero
x ≤+ y = x <+ y ⊎ x ≡ y

minimum+ : K+ → K+ → K+
minimum+ x y with S+.compare x y
minimum+ x y | tri< a ¬b ¬c = x
minimum+ x .x | tri≈ ¬a refl ¬c = x
minimum+ x y | tri> ¬a ¬b c = y

minimum+-correct : ∀ x y → minimum+ x y ≤+ x × minimum+ x y ≤+ y
minimum+-correct x y with S+.compare x y
minimum+-correct x y | tri< a ¬b ¬c = inj₂ refl , inj₁ a
minimum+-correct x .x | tri≈ ¬a refl ¬c = inj₂ refl , inj₂ refl
minimum+-correct x y | tri> ¬a ¬b c = inj₁ c , inj₂ refl

z<+x∧z<+y⇒z<minimum+ : ∀ {x y z} → z <+ x → z <+ y → z <+ minimum+ x y
z<+x∧z<+y⇒z<minimum+ {x} {y} z<+x z<+y with S+.compare x y
z<+x∧z<+y⇒z<minimum+ z<+x z<+y | tri< a ¬b ¬c = z<+x
z<+x∧z<+y⇒z<minimum+ z<+x z<+y | tri≈ ¬a refl ¬c = z<+x
z<+x∧z<+y⇒z<minimum+ z<+x z<+y | tri> ¬a ¬b c = z<+y

minimum+-same : ∀ x → minimum+ x x ≡ x
minimum+-same x with S+.compare x x
minimum+-same x | tri< a ¬b ¬c = refl
minimum+-same x | tri≈ ¬a refl ¬c = refl
minimum+-same x | tri> ¬a ¬b c = refl

minimum+-symmetric : ∀ x y → minimum+ x y ≡ minimum+ y x
minimum+-symmetric x y with S+.compare x y | S+.compare y x
minimum+-symmetric x y | tri< a ¬b ¬c | tri< d ¬e ¬f = ⊥-elim (¬f a)
minimum+-symmetric x .x | tri< a ¬b ¬c | tri≈ ¬d refl ¬f = ⊥-elim (¬b refl)
minimum+-symmetric x y | tri< a ¬b ¬c | tri> ¬d ¬e f = refl
minimum+-symmetric .y y | tri≈ ¬a refl ¬c | tri< d ¬e ¬f = ⊥-elim (¬e refl)
minimum+-symmetric x .x | tri≈ ¬a refl ¬c | tri≈ ¬d refl ¬f = refl
minimum+-symmetric .y y | tri≈ ¬a refl ¬c | tri> ¬d ¬e f = ⊥-elim (¬e refl)
minimum+-symmetric x y | tri> ¬a ¬b c | tri< d ¬e ¬f = refl
minimum+-symmetric x .x | tri> ¬a ¬b c | tri≈ ¬d refl ¬f = ⊥-elim (¬b refl)
minimum+-symmetric x y | tri> ¬a ¬b c | tri> ¬d ¬e f = ⊥-elim (¬d c)

{- Ordered Key-Value Store -}
data Store : (min : K+) → Set where
  ε : Store ⊤ᴷ
  _⇒_⊣_∷_ : {min : K+} (k : K) (v : V) → [ k ] <+ min → Store min → Store [ k ]

data _∈_ : {min : K+} → K → Store min → Set where
  head : {min : K+} {k : K} {v : V} {p : [ k ] <+ min} {st : Store min} → k ∈ (k ⇒ v ⊣ p ∷ st)
  tail : {min : K+} {k k′ : K} {v : V} {p : [ k′ ] <+ min} {st : Store min} → k ∈ st → k ∈ (k′ ⇒ v ⊣ p ∷ st)

_∉_ : {min : K+} → K → Store min → Set
k ∉ st = ¬ (k ∈ st)

min≤all : {min : K+} {k : K} {st : Store min} → k ∈ st → min ≤+ [ k ]
min≤all head = inj₂ refl
min≤all (tail pos) with min≤all pos
min≤all (tail {p = p} pos) | inj₁ x = inj₁ (S+.trans p x)
min≤all (tail {p = p} pos) | inj₂ refl = inj₁ p

min≤all′ : {min : K+} {k : K} {st : Store min} → k ∈ st → ¬ ([ k ] <+ min)
min≤all′ pos = x≤y→¬y<x _<+_ S+.isStrictPartialOrder (min≤all pos)

∈-unique : {min : K+} {k : K} (st : Store min) → (p q : k ∈ st) → p ≡ q
∈-unique ε () ()
∈-unique {k = k} (.k ⇒ v ⊣ x ∷ st) head head = refl
∈-unique {k = k} (.k ⇒ v ⊣ x ∷ st) head (tail q) = ⊥-elim (min≤all′ q x)
∈-unique {.([ k ])} {k} (.k ⇒ v ⊣ x ∷ st) (tail p) head = ⊥-elim (min≤all′ p x)
∈-unique (k₁ ⇒ v ⊣ x ∷ st) (tail p) (tail q) = cong tail (∈-unique st p q)

prove-∉-head∧tail : {min : K+} {k k′ : K} {v : V} {p : [ k′ ] <+ min} {st : Store min} → k ≢ k′ → k ∉ st → k ∉ (k′ ⇒ v ⊣ p ∷ st)
prove-∉-head∧tail k≢k′ k∉st head = k≢k′ refl
prove-∉-head∧tail k≢k′ k∉st (tail is-∈) = k∉st is-∈

prove-∉-<min : {min : K+} {k k′ : K} {v : V} {p : [ k′ ] <+ min} {st : Store min} → k < k′ → k ∉ (k′ ⇒ v ⊣ p ∷ st)
prove-∉-<min k<k′ head = S.irrefl refl k<k′
prove-∉-<min k<k′ (tail {p = p} pos) = min≤all′ pos (S+.trans <+[ k<k′ ] p)

search : {min : K+} (st : Store min) (k : K) → Dec (k ∈ st)
search ε k = no (λ ())
search (k′ ⇒ v ⊣ x ∷ st) k with S.compare k k′
search (k′ ⇒ v ⊣ x ∷ st) k | tri< a ¬b ¬c = no (prove-∉-<min a)
search (k ⇒ v ⊣ x ∷ st) .k | tri≈ ¬a refl ¬c = yes head
search (k′ ⇒ v ⊣ x ∷ st) k | tri> ¬a ¬b c with search st k
search (k′ ⇒ v ⊣ x ∷ st) k | tri> ¬a ¬b c | yes k∈st = yes (tail k∈st)
search (k′ ⇒ v ⊣ x ∷ st) k | tri> ¬a ¬b c | no k∉st = no (prove-∉-head∧tail ¬b k∉st)

lookup : {k : K} {min : K+} {st : Store min} → k ∈ st → V
lookup (head {v = v}) = v
lookup (tail pos) = lookup pos

find : {min : K+} (st : Store min) (k : K) → Maybe V
find st k with search st k
find st k | yes pos = just (lookup pos)
find st k | no ¬p = nothing

insert : {min : K+} (st : Store min) (k : K) → V → Store (minimum+ min [ k ])
insert ε k v = k ⇒ v ⊣ [ k ]<⊤ ∷ ε
insert (k ⇒ v ⊣ x ∷ st) l w with S.compare k l
insert (k ⇒ v ⊣ x ∷ st) l w | tri< a ¬b ¬c = k ⇒ v ⊣ z<+x∧z<+y⇒z<minimum+ x <+[ a ] ∷ insert st l w
insert (.l ⇒ v ⊣ x ∷ st) l w | tri≈ ¬a refl ¬c = l ⇒ w ⊣ x ∷ st
insert (k ⇒ v ⊣ x ∷ st) l w | tri> ¬a ¬b c = l ⇒ w ⊣ <+[ c ] ∷ (k ⇒ v ⊣ x ∷ st)

insert-adds-key : {min : K+} (st : Store min) (k : K) (v : V) → k ∈ insert st k v
insert-adds-key ε k v = head
insert-adds-key (k ⇒ v ⊣ x ∷ st) l w with S.compare k l
insert-adds-key (k ⇒ v ⊣ x ∷ st) l w | tri< a ¬b ¬c = tail (insert-adds-key st l w)
insert-adds-key (.l ⇒ v ⊣ x ∷ st) l w | tri≈ ¬a refl ¬c = head
insert-adds-key (k ⇒ v ⊣ x ∷ st) l w | tri> ¬a ¬b c = head

insert-changes-value : {min : K+} (st : Store min) (k : K) (v : V)
                     → (pos : k ∈ insert st k v)
                     → lookup pos ≡ v
insert-changes-value ε k v head = refl
insert-changes-value ε k v (tail ())
insert-changes-value (k ⇒ v ⊣ x ∷ st) l w pos with S.compare k l
insert-changes-value (.l ⇒ v ⊣ x ∷ st) l w head | tri< a ¬b ¬c
  = ⊥-elim (¬b refl)
insert-changes-value (k ⇒ v ⊣ x ∷ st) l w (tail pos) | tri< a ¬b ¬c
  = insert-changes-value st l w pos
insert-changes-value (.l ⇒ v ⊣ x ∷ st) l w pos | tri≈ ¬a refl ¬c with ∈-unique _ head pos
insert-changes-value (.l ⇒ v ⊣ x ∷ st) l w .head | tri≈ ¬a refl ¬c | refl
  = refl
insert-changes-value (k ⇒ v ⊣ x ∷ st) l w pos | tri> ¬a ¬b c with ∈-unique _ head pos
insert-changes-value (k ⇒ v ⊣ x ∷ st) l w .head | tri> ¬a ¬b c | refl
  = refl

insert-preserves-keys : {min : K+} (st : Store min) (k : K) (v : V)
                      → ∀ l → l ∈ st
                      → l ∈ insert st k v
insert-preserves-keys ε k v l ()
insert-preserves-keys (k ⇒ v ⊣ x ∷ st) l w m pos with S.compare k l
insert-preserves-keys (.m ⇒ v ⊣ x ∷ st) l w m head | tri< a ¬b ¬c
  = head
insert-preserves-keys (k ⇒ v ⊣ x ∷ st) l w m (tail pos) | tri< a ¬b ¬c
  = tail (insert-preserves-keys st l w m pos)
insert-preserves-keys (.m ⇒ v ⊣ x ∷ st) .m w m head | tri≈ ¬a refl ¬c
  = head
insert-preserves-keys (.l ⇒ v ⊣ x ∷ st) l w m (tail pos) | tri≈ ¬a refl ¬c
  = tail pos
insert-preserves-keys (k ⇒ v ⊣ x ∷ st) l w m pos | tri> ¬a ¬b c
  = tail pos

insert-preserves-most-values : {min : K+} (st : Store min) (k : K) (v : V)
                             → ∀ l → (l∈st : l ∈ st) → k ≢ l
                             → let l∈insert = insert-preserves-keys st k v l l∈st in
                                lookup l∈st ≡ lookup l∈insert
insert-preserves-most-values ε k v l () k≢l
insert-preserves-most-values (k ⇒ v ⊣ x ∷ st) l w m m∈st l≢m with S.compare k l
insert-preserves-most-values (.m ⇒ v ⊣ x ∷ st) l w m head l≢m | tri< a ¬b ¬c
  = refl
insert-preserves-most-values (k ⇒ v ⊣ x ∷ st) l w m (tail m∈st) l≢m | tri< a ¬b ¬c
  = insert-preserves-most-values st l w m m∈st l≢m
insert-preserves-most-values (.m ⇒ v ⊣ x ∷ st) l w m head l≢m | tri≈ ¬a b ¬c
  = ⊥-elim (l≢m (sym b))
insert-preserves-most-values (.l ⇒ v ⊣ x ∷ st) l w m (tail m∈st) l≢m | tri≈ ¬a refl ¬c
  = refl
insert-preserves-most-values (k ⇒ v ⊣ x ∷ st) l w m m∈st l≢m | tri> ¬a ¬b c
  = refl

fromList : List (K × V) → ∃ Store
fromList [] = ⊤ᴷ , ε
fromList (x ∷ xs) with fromList xs
fromList ((k , v) ∷ xs) | min , st = minimum+ min [ k ] , insert st k v

toList : {min : K+} → Store min → List (K × V)
toList ε = []
toList (k ⇒ v ⊣ x ∷ st) = (k , v) ∷ toList st

merge : {min₁ min₂ : K+} (a : Store min₁) (b : Store min₂) → Store (minimum+ min₁ min₂)
merge ε ε = ε
merge ε (k ⇒ v ⊣ x ∷ b) = k ⇒ v ⊣ x ∷ b
merge (k ⇒ v ⊣ x ∷ a) ε = k ⇒ v ⊣ x ∷ a
merge (k ⇒ v ⊣ x ∷ sa) (l ⇒ w ⊣ y ∷ sb) with S.compare k l
merge (_⇒_⊣_∷_ {m} k v x sa) (_⇒_⊣_∷_  {n} l w y sb) | tri< a ¬b ¬c
  = k ⇒ v
    ⊣ z<+x∧z<+y⇒z<minimum+ (z<+x∧z<+y⇒z<minimum+ x (S+.trans <+[ a ] y)) <+[ a ]
    ∷ insert (merge sa sb) l w
merge (k ⇒ v ⊣ x ∷ sa) (.k ⇒ w ⊣ y ∷ sb) | tri≈ ¬a refl ¬c
  = k ⇒ v
    ⊣ z<+x∧z<+y⇒z<minimum+ x y
    ∷ merge sa sb
merge (k ⇒ v ⊣ x ∷ sa) (l ⇒ w ⊣ y ∷ sb) | tri> ¬a ¬b c
  = l ⇒ w
    ⊣ z<+x∧z<+y⇒z<minimum+ (z<+x∧z<+y⇒z<minimum+ (S+.trans <+[ c ] x) y) <+[ c ]
    ∷ insert (merge sa sb) k v

{-
merge-symmetric : {m n : K+} (a : Store m) (b : Store n)
                → merge a b ≡ subst Store (minimum+-symmetric n m) (merge b a)
merge-symmetric ε ε = refl
merge-symmetric ε (k ⇒ v ⊣ x ∷ b) = refl
merge-symmetric (k ⇒ v ⊣ x ∷ a) ε = refl
merge-symmetric (k ⇒ v ⊣ x ∷ sa) (l ⇒ w ⊣ y ∷ sb) with S.compare k l
... | cmp = {!!}
-}
