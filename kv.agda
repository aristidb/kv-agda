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

data K+ : Set where
  ⊥ᴷ : K+
  [_] : K → K+
  ⊤ᴷ : K+

[]≡→≡ : {x y : K} → [ x ] ≡ [ y ] → x ≡ y
[]≡→≡ refl = refl

data _<+_ : Rel K+ Level.zero where
  ⊥<⊤ : ⊥ᴷ <+ ⊤ᴷ
  ⊥<[_] : (k : K) → ⊥ᴷ <+ [ k ]
  [_]<⊤ : (k : K) → [ k ] <+ ⊤ᴷ
  <+[_] : {i j : K} → i < j → [ i ] <+ [ j ]

<+[]→< : {x y : K} → [ x ] <+ [ y ] → x < y
<+[]→< <+[ p₁ ] = p₁

--map-Tri : {A : Set} {_≈_ _<_ : Rel A Level.zero} {x y : A} → Tri (x < y) (x ≈ y) (y < x) 

k+Order : IsStrictTotalOrder _≡_ _<+_
k+Order = record { isEquivalence = isEquivalence; trans = trans+; compare = compare+; <-resp-≈ = resp₂ _ }
  where
    module S = IsStrictTotalOrder keyOrder

    trans+ : Transitive _<+_
    trans+ ⊥<⊤ ()
    trans+ ⊥<[ k₁ ] [ .k₁ ]<⊤ = ⊥<⊤
    trans+ ⊥<[ k₁ ] <+[ q ] = ⊥<[ _ ]
    trans+ [ k₁ ]<⊤ ()
    trans+ (<+[_] p) [ _ ]<⊤ = [ _ ]<⊤
    trans+ <+[ p ] <+[ q ] = <+[ S.trans p q ]

    compare+ : Trichotomous _≡_ _<+_
    compare+ ⊥ᴷ ⊥ᴷ = tri≈ (λ ()) refl (λ ())
    compare+ ⊥ᴷ [ x ] = tri< ⊥<[ x ] (λ ()) (λ ())
    compare+ ⊥ᴷ ⊤ᴷ = tri< ⊥<⊤ (λ ()) (λ ())
    compare+ [ x ] ⊥ᴷ = tri> (λ ()) (λ ()) ⊥<[ x ]
    compare+ [ x ] ⊤ᴷ = tri< [ x ]<⊤ (λ ()) (λ ())
    compare+ ⊤ᴷ ⊥ᴷ = tri> (λ ()) (λ ()) ⊥<⊤
    compare+ ⊤ᴷ [ x ] = tri> (λ ()) (λ ()) [ x ]<⊤
    compare+ ⊤ᴷ ⊤ᴷ = tri≈ (λ ()) refl (λ ())
    compare+ [ x ] [ y ] with S.compare x y
    compare+ [ x ] [ y ] | tri< a ¬b ¬c = tri< <+[ a ] (¬b ∘ []≡→≡) (¬c ∘ <+[]→<)
    compare+ [ x ] [ y ] | tri≈ ¬a b ¬c = tri≈ (¬a ∘ <+[]→<) (cong [_] b) (¬c ∘ <+[]→<)
    compare+ [ x ] [ y ] | tri> ¬a ¬b c = tri> (¬a ∘ <+[]→<) (¬b ∘ []≡→≡) <+[ c ]

{- Ordered Key-Value Store -}
data Store : Set where
  ε : Store

