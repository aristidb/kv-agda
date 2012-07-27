module test where

open import Data.Nat
import Data.Nat.Properties as NP
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.List
open import Data.Product
open import Data.Maybe

import kv

open StrictTotalOrder NP.strictTotalOrder

open kv ℕ isStrictTotalOrder
module n = kv ℕ isStrictTotalOrder

x : _
x = proj₂ (fromList ((4 , 5) ∷ (1 , 2) ∷ []))

y : _
y = proj₂ (fromList ((1 , 2) ∷ (3 , 4) ∷ (5 , 6) ∷ []))

z : _
z = merge x y

z-list : toList z ≡ (1 , 2) ∷ (3 , 4) ∷ (4 , 5) ∷ (5 , 6) ∷ []
z-list = refl

t1 : 1 ∈ x
t1 = kv.head

t2 : 2 ∉ x
t2 (kv.tail (kv.tail ()))

t4 : 4 ∈ x
t4 = kv.tail kv.head

search-1 : search x 1 ≡ yes t1
search-1 = refl

search-2 : ∃ λ p → search x 2 ≡ no p
search-2 = , refl

search-4 : search x 4 ≡ yes t4
search-4 = refl

lookup-1 : lookup t1 ≡ 2
lookup-1 = refl

lookup-4 : lookup t4 ≡ 5
lookup-4 = refl

r1 : _
r1 = proj₂ (proj₂ (remove t1))

r1-list : toList r1 ≡ (4 , 5) ∷ []
r1-list = refl

zipped : _
zipped = n.zipWith _,_ x y

zipped-list : toList zipped ≡ (1 , just 2 , just 2) ∷ (3 , nothing , just 4) ∷ (4 , just 5 , nothing) ∷ (5 , nothing , just 6) ∷ []
zipped-list = refl
