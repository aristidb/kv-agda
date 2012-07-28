import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PE hiding ([_])

module patch
  (K V : Set)
  {_<_ : Rel K Level.zero}
  (keyOrder : IsStrictTotalOrder _≡_ _<_)
  (valueEq : IsDecEquivalence {A = V} _≡_)
where

import kv
open import Data.Maybe
open import Data.Product hiding (map)
open import Relation.Nullary
open import Function using (_∘_)
open import Category.Functor

open RawFunctor {Level.zero} Data.Maybe.functor

module VEq = IsDecEquivalence valueEq
module MVEq = DecSetoid (Data.Maybe.decSetoid (record { isDecEquivalence = valueEq }))

open kv K keyOrder

record Op : Set where
  constructor op
  field old : Maybe V
        new : Maybe V

inv : Op → Op
inv (op old new) = op new old

_⊙_ : Op → Op → Maybe Op
op oldF newF ⊙ op oldG newG with oldF MVEq.≟ newG
op oldF newF ⊙ op oldG newG | yes p = just (op oldG newG)
op oldF newF ⊙ op oldG newG | no ¬p = nothing

_⊙′_ : Maybe Op → Maybe Op → Maybe Op
just f ⊙′ just g = f ⊙ g
just f ⊙′ nothing = just f
nothing ⊙′ g = g

single : Maybe V → Op → Maybe (Maybe V)
single old (op old′ new) with old MVEq.≟ old′
single old (op old′ new) | yes p = just new
single old (op old′ new) | no ¬p = nothing

single′ : Maybe V → Maybe Op → Maybe (Maybe V)
single′ old (just x) = single old x
single′ old nothing = just old

--single-inv : ∀ op → 

apply : ∀ {m n} → Store V m → Store Op n → Maybe (∃ (Store V))
apply c p = (unwrap ∘ catMaybes) <$> sequence (zipWith single′ c p)
  where unwrap : _ → _
        unwrap (n , m≤n , st) = n , st

id : Store Op ⊤ᴷ
id = ε

invert : ∀ {m} → Store Op m → Store Op m
invert = map inv

invert-correct : ∀ {m n} (cont : Store V m) (patch : Store Op n)
               → {res : ∃ (Store V)} → apply cont patch ≡ just res
               → apply (proj₂ res) (invert patch) ≡ just (, cont)
invert-correct cont kv.ε {res} valid = {!!}
invert-correct cont (k kv.⇒ v ⊣ x ∷ patch) {proj₁ , proj₂} valid = {!!}

compose : ∀ {m n} → Store Op m → Store Op n → Maybe (Store Op (minimum+ m n))
compose f g = sequence (zipWith _⊙′_ f g)

-- ?
transform : {!!}
transform = {!!}
