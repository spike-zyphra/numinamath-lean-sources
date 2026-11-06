import Mathlib

theorem inequalities_121789 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hsum : x + y ≤ 1) :
    x^2 + 8 * x^2 * y^2 + y^2 ≤ 1 := by 
  have h1 : 0 ≤ y := hy
  have h2 : 0 ≤ x := hx
  have h3 : x + y ≤ 1 := hsum
  have h4 : (x + y) ^ 2 ≤ (1 : ℝ) := by
    nlinarith
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 1), sq_nonneg (x - 1 / 2), sq_nonneg (y - 1 / 2), 
            mul_nonneg hx hy, mul_nonneg hx (show 0 ≤ 1 - y by linarith), 
            mul_nonneg hy (show 0 ≤ 1 - x by linarith), 
            mul_nonneg (show 0 ≤ x * y by nlinarith) (show 0 ≤ (x + y) by nlinarith)]