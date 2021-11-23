module UCaps where

-- data Bool : Set where
--   true : Bool
--   false : Bool

-- ¬_ : Bool -> Bool
-- ¬_ true = false
-- ¬ false = true

data BL : Set where
  true : BL
  false : BL
  not : BL -> BL

interp : BL -> BL
interp (not b) = b
interp true = true
interp false = false

data _≡_ {A : Set}(x : A) : A -> Set where
  refl : x ≡ x

data _≠_ : BL -> BL -> Set where
  t≠f : true ≠ false
  f≠t : false ≠ true

data Equal? (n m : BL) : Set where
  eq : n ≡ m -> Equal? n m
  neq : n ≠ m -> Equal? n m

equal? : (n m : BL) -> Equal? n m
equal? true true = eq refl
equal? false false = eq refl
equal? true false = neq t≠f
equal? false true = neq f≠t
