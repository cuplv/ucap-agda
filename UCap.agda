module UCap where

open import Relation.Binary.PropositionalEquality using (_≡_)

record ⊗-Laws (c : Set)(id : c)(uni : c)(_⊗_ : c -> c -> c) : Set₁ where
  field
    assoc : ∀ x y z -> ((x ⊗ y) ⊗ z) ≡ (x ⊗ (y ⊗ z))
    comm : ∀ x y -> (x ⊗ y) ≡ (y ⊗ x)
    idr : ∀ x -> (x ⊗ id) ≡ x
    idl : ∀ x -> (id ⊗ x) ≡ x
    unir : ∀ x -> (x ⊗ uni) ≡ uni
    unil : ∀ x -> (uni ⊗ x) ≡ uni

record UCap (c : Set) : Set₁ where
  infixl 7 _⊗_
  field
    id : c
    uni : c
    _⊗_ : c -> c -> c
    ⊗-laws : ⊗-Laws c id uni _⊗_
