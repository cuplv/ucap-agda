module UCaps where

open import Data.Nat using (ℕ; _+_; _*_)

open import Data.Nat.Properties using (+-comm; +-identityʳ;  +-identityˡ)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

ex₁ : 3 + 5 ≡ 8
ex₁ = refl

data Counter : Set where
  counter : ℕ -> ℕ -> Counter

_⊗_ : Counter -> Counter -> Counter
counter a1 s1 ⊗ counter a2 s2 = counter (a1 + a2) (s1 + s2)

id : Counter
id = counter 0 0

open Relation.Binary.PropositionalEquality using (cong; cong₂; module ≡-Reasoning)

⊗-idr : ∀ x -> x ⊗ id ≡ x
⊗-idr (counter a s) = begin
  counter (a + 0) (s + 0) ≡⟨ cong₂ counter
                                   (+-identityʳ a)
                                   (+-identityʳ s) ⟩
  counter a s ∎
  where open ≡-Reasoning

⊗-idl : ∀ x -> id ⊗ x ≡ x
⊗-idl (counter a s) = begin
  counter (0 + a) (0 + s) ≡⟨ cong₂ counter
                                   (+-identityˡ a)
                                   (+-identityˡ s) ⟩
  counter a s ∎
  where open ≡-Reasoning
