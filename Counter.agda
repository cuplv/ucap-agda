module Counter where

open import Data.Nat using (ℕ; _+_)

open import Data.Nat.Properties using (+-comm; +-identityʳ; +-identityˡ)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open Relation.Binary.PropositionalEquality using (cong; cong₂; module ≡-Reasoning)

open import UCap

ex₁ : 3 + 5 ≡ 8
ex₁ = refl

data Bound : Set where
  fin : ℕ -> Bound
  inf : Bound

zero : Bound
zero = fin 0

_++_ : Bound -> Bound -> Bound
fin x ++ fin y = fin (x + y)
fin x ++ inf = inf
inf ++ fin y = inf
inf ++ inf = inf

++-comm : ∀ x y -> x ++ y ≡ y ++ x
++-comm (fin x) (fin y) = cong fin (+-comm x y)
++-comm (fin x) inf = refl
++-comm inf (fin y) = refl
++-comm inf inf = refl

++-idr : ∀ x -> x ++ zero ≡ x
++-idr (fin x) = cong fin (+-identityʳ x)
++-idr inf = refl

++-idl : ∀ x -> zero ++ x ≡ x
++-idl (fin x) = cong fin (+-identityˡ x)
++-idl inf = refl

++-unir : ∀ x -> x ++ inf ≡ inf
++-unir (fin x) = refl
++-unir inf = refl

++-unil : ∀ x -> inf ++ x ≡ inf
++-unil (fin x) = refl
++-unil inf = refl

data Counter : Set where
  counter : Bound -> Bound -> Counter

_⊗_ : Counter -> Counter -> Counter
counter a1 s1 ⊗ counter a2 s2 = counter (a1 ++ a2) (s1 ++ s2)

id : Counter
id = counter zero zero

⊗-idr : ∀ c -> c ⊗ id ≡ c
⊗-idr (counter a s) = cong₂ counter (++-idr a) (++-idr s)

⊗-idl : ∀ c -> id ⊗ c ≡ c
⊗-idl (counter a s) = begin
  counter (zero ++ a) (zero ++ s)
    ≡⟨ cong₂ counter (++-idl a) (++-idl s) ⟩
  counter a s ∎
  where open ≡-Reasoning

uni : Counter
uni = counter inf inf

⊗-unir : ∀ c -> c ⊗ uni ≡ uni
⊗-unir (counter a s) = cong₂ counter (++-unir a) (++-unir s)

⊗-unil : ∀ c -> uni ⊗ c ≡ uni
⊗-unil (counter a s) = cong₂ counter (++-unil a) (++-unil s)

assoc : ∀ x y z -> ((x ⊗ y) ⊗ z) ≡ (x ⊗ (y ⊗ z))
assoc = _

comm : ∀ x y -> x ⊗ y ≡ y ⊗ x
comm = _

Counter-⊗-laws : ⊗-Laws Counter id uni _⊗_
Counter-⊗-laws = record
  { assoc = assoc
  ; comm = comm
  ; idr = ⊗-idr
  ; idl = ⊗-idl
  ; unir = ⊗-unir
  ; unil = ⊗-unil
  }

CounterCap : UCap Counter
CounterCap = record
  { id = id
  ; uni = uni
  ; _⊗_ = _⊗_
  ; ⊗-laws = Counter-⊗-laws
  }
