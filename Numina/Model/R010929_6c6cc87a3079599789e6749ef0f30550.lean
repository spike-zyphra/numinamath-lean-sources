import Mathlib

theorem algebra_608844 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : x^2 + y^2 + x * y = 1) (h2 : y^2 + z^2 + y * z = 4) (h3 : z^2 + x^2 + z * x = 5) :
    x + y + z = Real.sqrt (5 + 2 * Real.sqrt 3) := by

  have eq4 : (x + y + z) ^ 2 = 5 + 2 * Real.sqrt 3 := by
    -- We will derive that ((x + y + z) ^ 2 - (5 + 2 * Real.sqrt 3)) * ((x + y + z) ^ 2 - (5 - 2 * Real.sqrt 3)) = 0.
    have eq5 : ((x + y + z) ^ 2 - (5 + 2 * Real.sqrt 3)) * ((x + y + z) ^ 2 - (5 - 2 * Real.sqrt 3)) = 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith)]
    -- Now, either (x + y + z) ^ 2 = 5 + 2 * Real.sqrt 3 or (x + y + z) ^ 2 = 5 - 2 * Real.sqrt 3.
    cases' (mul_eq_zero.mp eq5) with h4 h5
    · -- Case where (x + y + z) ^ 2 - (5 + 2 * Real.sqrt 3) = 0.
      linarith
    · -- Case where (x + y + z) ^ 2 - (5 - 2 * Real.sqrt 3) = 0.
      -- This leads to a contradiction since (x + y + z) ^ 2 > 0.
      have eq6 : (x + y + z) ^ 2 = 5 - 2 * Real.sqrt 3 := by linarith
      have h12 : (x + y + z) ^ 2 > 0 := by positivity
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith), Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by linarith), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]

  have h7 : x + y + z ≥ 0 := by positivity
  have h8 : x + y + z = Real.sqrt (5 + 2 * Real.sqrt 3) := by
    have h9 : (x + y + z) ^ 2 = 5 + 2 * Real.sqrt 3 := eq4
    have h10 : x + y + z ≥ 0 := h7
    have h11 : x + y + z = Real.sqrt (5 + 2 * Real.sqrt 3) := by
      rw [← h9]
      field_simp [Real.sqrt_sq_eq_abs, abs_of_nonneg h7]
    exact h11
  exact h8