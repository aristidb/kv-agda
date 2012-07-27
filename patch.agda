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
open import Data.Product
open import Relation.Nullary
open import Function
open import Category.Functor

open RawFunctor {Level.zero} Data.Maybe.functor

module VEq = IsDecEquivalence valueEq
module MVEq = DecSetoid (Data.Maybe.decSetoid (record { isDecEquivalence = valueEq }))

open kv K keyOrder

record Op : Set where
  constructor op
  field old : Maybe V
        new : Maybe V

{-
apply-Op : ∀ {m} → Store V m → K → Op → Maybe (∃ (Store V))
apply-Op st k (op old new) with search st k
apply-Op st k (op (just old) new) | yes p with VEq._≟_ old (lookup p)
apply-Op st k (op (just old) new) | yes p | yes q with remove p
... | _ , _ , st′ = just (insert-maybe st′ k new)
apply-Op st k (op (just old) new) | yes p | no ¬q = nothing
apply-Op st k (op nothing new) | yes p = nothing
apply-Op st k (op (just old) new) | no ¬p = nothing
apply-Op st k (op nothing new) | no ¬p = just (insert-maybe st k new)
-}

single : Maybe V → Op → Maybe (Maybe V)
single old (op old′ new) with old MVEq.≟ old′
single old (op old′ new) | yes p = just new
single old (op old′ new) | no ¬p = nothing

single′ : Maybe V → Maybe Op → Maybe (Maybe V)
single′ old (just x) = single old x
single′ old nothing = just old

{-
-- TODO: iterate over both Store's in the same go?
apply : ∀ {m n} → Store V m → Store Op n → Maybe (∃ (Store V))
apply cont kv.ε = just (, cont)
apply cont (k kv.⇒ v ⊣ p ∷ patch) with apply-Op cont k v
apply cont (k kv.⇒ v ⊣ p ∷ patch) | just (_ , cont′) = apply cont′ patch
apply cont (k kv.⇒ v ⊣ p ∷ patch) | nothing = nothing
-}

apply : ∀ {m n} → Store V m → Store Op n → Maybe (∃ (Store V))
apply c p = (unwrap ∘ catMaybes) <$> sequence (zipWith single′ c p)
  where unwrap : _ → _
        unwrap (n , m≤n , st) = n , st
