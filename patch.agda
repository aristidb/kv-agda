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
open import Data.Sum hiding (map)
open import Relation.Nullary
open import Category.Functor

open RawFunctor {Level.zero} Data.Maybe.functor

module VEq = IsDecEquivalence valueEq

open kv K keyOrder

record Op (old : Maybe V) : Set where
  constructor op
  field new : Maybe V

id : ∀ {old} → Op old
id {x} = op x

inv : ∀ {old} → Op old → ∃ Op
inv {old} o = Op.new o , op old

apply : (x : Maybe V) → Op x → Maybe V
apply _ y = Op.new y

applyMaybe : (x : Maybe V) → Maybe (Op x) → Maybe V
applyMaybe x nothing = x
applyMaybe x (just y) = apply x y

compose : ∀ {old} → (a : Op old) → Op (Op.new a) → Op old
compose _ b = op (Op.new b)

apply-compose : ∀ old (a : Op old) (b : Op (Op.new a))
              → apply old (compose a b) ≡ apply (apply old a) b
apply-compose old a b = refl

Patch : ∀ {m} → Store′ V m → K+ → Set
Patch st = Store (λ k → Op {!!})

idP : ∀ {m} {st : Store′ V m} → Patch st ⊤ᴷ
idP = ε

patch1 : ∀ {m n} → (st : Store′ V m) → Patch st n → Store′ (Maybe V) (minimum+ m n)
patch1 st p = zipWith {!applyMaybe!} st {!p!}

{-
inv : Op → Op
inv (op old new) = op new old

compat : Maybe V → Op → Set
compat x y = x ≡ Op.old y

apply : (x : Maybe V) (o : Op) → compat x o → Maybe V
apply _ o _ = Op.new o

compose : (f g : Op) → Op.new g ≡ Op.old f → Op
compose f g p = op (Op.old g) (Op.new f)

apply-compose : (f g : Op) (composable : Op.new g ≡ Op.old f)
              → (x : Maybe V) (applicable : compat x g)
              → apply x (compose f g composable) applicable ≡ apply (apply x g applicable) f composable
apply-compose f g composable x applicable = refl

Patch : K+ → Set
Patch min = Store Op min

patch-compatible : ∀ {m n} → Store V m → Patch n → Set
patch-compatible st P = ∀ {k} → (p : k ∈ P) → let old = Op.old (lookup p)
                        in Σ (k ∈ st) (λ pos → just (lookup pos) ≡ old)
                           ⊎ k ∉ st × nothing ≡ old

patch′ : ∀ {m n} (st : Store V m) (P : Patch n) → patch-compatible st P → Store (Maybe V) (minimum+ m n)
patch′ st P = {!!}

patch : ∀ {m n} (st : Store V m) (P : Patch n) → patch-compatible st P → ∃ (Store V)
patch st P c with catMaybes (patch′ st P c)
... | m , _ , st′ = m , st′

-}
