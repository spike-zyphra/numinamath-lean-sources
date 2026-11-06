import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_599874
  (x y z : ℝ)
  (hx : 0 ≤ x)
  (hy : 0 ≤ y)
  (hz : 0 ≤ z)
  (hsum : x + y + z = 1) :
  0 ≤ x * y + y * z + z * x - 2 * x * y * z ∧
  x * y + y * z + z * x - 2 * x * y * z ≤ 7 / 27 := by
  have h1 : z = 1 - x - y := by linarith
  rw [h1]
  constructor
  · -- First part: $0 \leqslant x * y + y * z + z * x - 2 * x * y * z$
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - (1 - x - y)), sq_nonneg (x - (1 - x - y)), 
            mul_nonneg hx hy, mul_nonneg hy (show 0 ≤ 1 - x - y by nlinarith), 
            mul_nonneg hx (show 0 ≤ 1 - x - y by nlinarith)]
  · -- Second part: $x * y + y * z + z * x - 2 * x * y * z \leqslant \frac{7}{27}$
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - (1 - x - y)), sq_nonneg (x - (1 - x - y)), 
            sq_nonneg (x + y - (1 - x - y)), 
            mul_nonneg hx hy, mul_nonneg hy (show 0 ≤ 1 - x - y by nlinarith), 
            mul_nonneg hx (show 0 ≤ 1 - x - y by nlinarith),
            sq_nonneg (x - 1 / 3), sq_nonneg (y - 1 / 3), sq_nonneg ((1 - x - y) - 1 / 3)]