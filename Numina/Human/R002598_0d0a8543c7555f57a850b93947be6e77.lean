import Mathlib

/- (3 * 5)/(9 * 11) * (7 * 9 * 11)/(3 * 5 * 7)=
(A) 1   (B) 0   (C) 49  (D) 1/49  (E) 50 -/
theorem algebra_96021 : (3 * 5 / (9 * 11 : ℝ)) * (7 * 9 * 11 / (3 * 5 * 7)) = 1 := by ring
-- by associativity and commutativity properties of the field ℝ and by properties of multiplication
-- of fraction you can erase each term of the numerator with each of the denomiantor.