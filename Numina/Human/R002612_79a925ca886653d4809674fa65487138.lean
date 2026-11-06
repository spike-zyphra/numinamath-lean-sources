import Mathlib
open Real
/-Let o be an odd whole number and let n be any whole number. Which of the following statements about the whole
number (o^2 + no) is always true?
(A) it is always odd  (B) it is always even
(C) it is even only if n is even  (D) it is odd only if n is odd
(E) it is odd only if n is even-/
theorem number_theory_96349 (o n : ℤ) (ho : Odd o) :
Odd (o^2 + n * o) ↔ Even n := by
-- discussing the whether o is even or odd, obtaining the result of o^2, thus obtaining the goal
simp only [← Int.not_even_iff_odd, Int.even_add, Int.even_mul, Int.even_pow] at *
tauto