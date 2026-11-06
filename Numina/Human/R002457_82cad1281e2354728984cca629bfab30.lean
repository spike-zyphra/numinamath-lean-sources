import Mathlib

/- A two-inch cube (2×2×2) of silver weighs 3 pounds and is worth 200 dollars. 
How much is a three-inch cube of silver worth?
(A) 300 dollars(B) 375 dollars(C) 450 dollars(D) 560 dollars(E) 675 dollars -/
theorem algebra_93671 {x : ℝ} (hx : x = 200 / (2^3)) :
x * (3^3) = 675 := by
--x is the worth in dollars for each inch cube, there are 27 in a 3x3x3 cube.
  rw [hx]; norm_num