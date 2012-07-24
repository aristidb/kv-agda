import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_])

module kv
  (K V : Set)
  {_<_ : Rel K Level.zero}
  (keyOrder : IsStrictTotalOrder _≡_ _<_)
where

open import Data.Unit using (⊤ ; tt)
open import Data.Empty using (⊥)
open import Function using (_∘_)
open import Data.List hiding ([_])
open import Data.Product
open import Data.Sum
open import Relation.Nullary
import Relation.Binary.Props.StrictTotalOrder as STOP

data K+ : Set where
  [_] : K → K+
  ⊤ᴷ : K+

[]≡→≡ : {x y : K} → [ x ] ≡ [ y ] → x ≡ y
[]≡→≡ refl = refl

data _<+_ : Rel K+ Level.zero where
  [_]<⊤ : (k : K) → [ k ] <+ ⊤ᴷ
  <+[_] : {i j : K} → i < j → [ i ] <+ [ j ]

<+[]→< : {x y : K} → [ x ] <+ [ y ] → x < y
<+[]→< <+[ p₁ ] = p₁

module S = IsStrictTotalOrder keyOrder

SO : StrictTotalOrder _ _ _
SO = record { Carrier = K; _≈_ = _≡_; _<_ = _<_; isStrictTotalOrder = keyOrder }

module SOP = STOP SO

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
    compare+ [ x ] [ y ] | tri< a ¬b ¬c = tri< <+[ a ] (¬b ∘ []≡→≡) (¬c ∘ <+[]→<)
    compare+ [ x ] [ y ] | tri≈ ¬a b ¬c = tri≈ (¬a ∘ <+[]→<) (cong [_] b) (¬c ∘ <+[]→<)
    compare+ [ x ] [ y ] | tri> ¬a ¬b c = tri> (¬a ∘ <+[]→<) (¬b ∘ []≡→≡) <+[ c ]

module S+ = IsStrictTotalOrder k+Order

S+O : StrictTotalOrder _ _ _
S+O = record { Carrier = K+; _≈_ = _≡_; _<_ = _<+_; isStrictTotalOrder = k+Order }

module S+OP = STOP S+O

_≤+_ : _
_≤+_ = S+OP._≤_

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
min≤all′ pos with min≤all pos
min≤all′ pos | inj₁ x = {!S+.irrefl !}
min≤all′ pos | inj₂ y = {!!}

prove-∉ : {min : K+} {k k′ : K} {v : V} {p : [ k′ ] <+ min} {st : Store min} → k ≢ k′ → k ∉ st → k ∉ (k′ ⇒ v ⊣ p ∷ st)
prove-∉ k≢k′ k∉st head = k≢k′ refl
prove-∉ k≢k′ k∉st (tail is-∈) = k∉st is-∈

prove-∉2 : {min : K+} {k k′ : K} {v : V} {p : [ k′ ] <+ min} {st : Store min} → k < k′ → k ∉ (k′ ⇒ v ⊣ p ∷ st)
prove-∉2 k<k′ head = S.irrefl refl k<k′
prove-∉2 k<k′ (tail pos) = {!prove-∈2 !}

search : {min : K+} (st : Store min) (k : K) → Dec (k ∈ st)
search st k = {!!}
{-
search ε k = no (λ ())
search (k′ ⇒ v ⊣ x ∷ st) k with S.compare k k′
search (k′ ⇒ v ⊣ x ∷ st) k | tri< a ¬b ¬c with search st k
search (k′ ⇒ v ⊣ x ∷ st) k | tri< a ¬b ¬c | yes p = yes (tail a p)
search (k′ ⇒ v ⊣ x ∷ st) k | tri< a ¬b ¬c | no ¬p = no (prove-∉ ¬b ¬p)
search (.k ⇒ v ⊣ x ∷ st) k | tri≈ ¬a refl ¬c = yes head
search (k′ ⇒ v ⊣ x ∷ st) k | tri> ¬a ¬b c = no {!!}
-}

lookup : {k : K} {min : K+} {st : Store min} → k ∈ st → V
lookup (head {v = v}) = v
lookup (tail pos) = lookup pos

{-
lookup {k} .(k ⇒ v ⊣ p ∷ st) (head .k v p st) = v
lookup {k} .(k′ ⇒ v ⊣ p ∷ st) (tail .k k′ v p q st pos) = lookup st pos
-}

{-
insert : {min : K+} → K × V → Store min → ∃ Store
insert (k , v) ε = [ k ] , k ⇒ v ⊣ [ k ]<⊤ ∷ ε
insert (k′ , v′) (k ⇒ v ⊣ p ∷ st) with S.compare k k′
insert (k′ , v′) (k ⇒ v ⊣ p ∷ st) | tri< a ¬b ¬c with insert (k′ , v′) st
insert (k′ , v′) (k ⇒ v ⊣ p ∷ st) | tri< a ¬b ¬c | k+ , st′ = [ k ] , k ⇒ v ⊣ {!!} ∷ st′
insert (.k , v′) (k ⇒ v ⊣ p ∷ st) | tri≈ ¬a refl ¬c = [ k ] , k ⇒ v′ ⊣ p ∷ st
insert (k′ , v′) (k ⇒ v ⊣ p ∷ st) | tri> ¬a ¬b c = [ k′ ] , k′ ⇒ v′ ⊣ <+[ c ] ∷ (k ⇒ v ⊣ p ∷ st)
-}

fromList : List (K × V) → ∃ Store
fromList [] = ⊤ᴷ , ε
fromList (x ∷ xs) with fromList xs
... | tl = {!!}
