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

module VEq = IsDecEquivalence valueEq
module MVEq = DecSetoid (Data.Maybe.decSetoid (record { isDecEquivalence = valueEq }))

module container = kv K V keyOrder

record KeyChange : Set where
  constructor keyChange
  field old : Maybe V
        new : Maybe V

apply-keyChange : ∀ {m} → container.Store m → K → KeyChange → Maybe (∃ container.Store)
apply-keyChange st k (keyChange old new) with container.search st k
apply-keyChange st k (keyChange (just old) new) | yes p with VEq._≟_ old (container.lookup p)
apply-keyChange st k (keyChange (just old) new) | yes p | yes q with container.remove p
... | _ , _ , st′ = just (container.insert-maybe st′ k new)
apply-keyChange st k (keyChange (just old) new) | yes p | no ¬q = nothing
apply-keyChange st k (keyChange nothing new) | yes p = nothing
apply-keyChange st k (keyChange (just old) new) | no ¬p = nothing
apply-keyChange st k (keyChange nothing new) | no ¬p = just (container.insert-maybe st k new)

module patch-kv = kv K KeyChange keyOrder

-- TODO: iterate over both Store's in the same go?
apply : ∀ {m n} → container.Store m → patch-kv.Store n → Maybe (∃ container.Store)
apply cont kv.ε = just (, cont)
apply cont (k kv.⇒ v ⊣ p ∷ patch) with apply-keyChange cont k v
apply cont (k kv.⇒ v ⊣ p ∷ patch) | just (_ , cont′) = apply cont′ patch
apply cont (k kv.⇒ v ⊣ p ∷ patch) | nothing = nothing
