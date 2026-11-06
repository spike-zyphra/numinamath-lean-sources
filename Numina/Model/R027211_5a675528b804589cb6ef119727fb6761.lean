import Mathlib

open Real

theorem inequalities_234813 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hsum : x + y + z = 1) :
    0 ≤ y * z + z * x + x * y - 2 * x * y * z ∧
    y * z + z * x + x * y - 2 * x * y * z ≤ 7 / 27 := by
  constructor
  · -- Prove lower bound
    have h1 : z = 1 - x - y := by linarith
    have hx2 : x = 1 - y - z := by linarith
    have hy2 : y = 1 - x - z := by linarith
    -- Now, substitute z = 1 - x - y in the expression
    rw [h1]
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - (1 - x - y)), sq_nonneg (y - (1 - x - y))]
  · -- Prove upper bound
    have h1 : z = 1 - x - y := by linarith
    have hx2 : x = 1 - y - z := by linarith
    have hy2 : y = 1 - x - z := by linarith
    -- Substitute z = 1 - x - y in the expression
    rw [h1]
    by_cases h : x ≤ y
    · -- Case where x ≤ y
      by_cases h4 : y ≤ z
      · -- Case where x ≤ y and y ≤ z
        nlinarith [ sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x + y - z), sq_nonneg (x - 1/3), sq_nonneg (y - 1/3), sq_nonneg (z - 1/3),
          mul_nonneg hx hy, mul_nonneg hx hz, mul_nonneg hy hz ]
      · -- Case where x ≤ y and y > z
        nlinarith [ sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x + y - z), sq_nonneg (x - 1/3), sq_nonneg (y - 1/3), sq_nonneg (z - 1/3),
          mul_nonneg hx hy, mul_nonneg hx hz, mul_nonneg hy hz ]
    · -- Case where x > y
      by_cases h6 : y ≤ z
      · -- Case where x > y and y ≤ z
        nlinarith [ sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x + y - z), sq_nonneg (x - 1/3), sq_nonneg (y - 1/3), sq_nonneg (z - 1/3),
          mul_nonneg hx hy, mul_nonneg hx hz, mul_nonneg hy hz ]
      · -- Case where x > y and y > z
        nlinarith [ sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x + y - z), sq_nonneg (x - 1/3), sq_nonneg (y - 1/3), sq_nonneg (z - 1/3),
          mul_nonneg hx hy, mul_nonneg hx hz, mul_nonneg hy hz ]