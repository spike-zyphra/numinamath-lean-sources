import Mathlib

theorem algebra_159395 {x y : ℝ} (hx : x ≥ -2 * y) (hy : y ≥ 0)
    (h1 : x + Real.sqrt (x + 2 * y) - 2 * y = 7 / 2) (h2 : x ^ 2 + x + 2 * y - 4 * y ^ 2 = 27 / 2) :
    x = 19 / 4 ∧ y = 17 / 8 := by
  have h3 : Real.sqrt (x + 2 * y) ≥ 0 := Real.sqrt_nonneg (x + 2 * y)
  have h4 : (Real.sqrt (x + 2 * y)) ^ 2 = x + 2 * y := Real.sq_sqrt (show x + 2 * y ≥ 0 by linarith)
  -- Solving the system using substitution as discussed
  have h5 : Real.sqrt (x + 2 * y) = 3 := by
    nlinarith [sq_nonneg (Real.sqrt (x + 2 * y) - 3), sq_nonneg (x - 19 / 4), sq_nonneg (y - 17 / 8), Real.sqrt_nonneg (x + 2 * y)]
  -- From h5, (Real.sqrt (x + 2 * y)) ^ 2 = 9, so x + 2 * y = 9
  have h6 : x + 2 * y = 9 := by
    have h7 : (Real.sqrt (x + 2 * y)) ^ 2 = x + 2 * y := Real.sq_sqrt (show x + 2 * y ≥ 0 by linarith)
    rw [h5] at h7
    nlinarith
  -- From h1 and h5: x + 3 - 2 * y = 7 / 2 => x - 2 * y = 1 / 2
  have h8 : x - 2 * y = 1 / 2 := by
    nlinarith [h5, h6, h1]
  -- Solving the system
  -- Adding equations: (x + 2 * y) + (x - 2 * y) = 9 + 1 / 2 => 2 * x = 19 / 2 => x = 19 / 4
  -- Substitute into x + 2 * y = 9: 19 / 4 + 2 * y = 9 => 2 * y = 17 / 4 => y = 17 / 8
  have hx1 : x = 19 / 4 := by
    nlinarith [h6, h8]
  have hy1 : y = 17 / 8 := by
    nlinarith [h6, hx1]
  exact ⟨hx1, hy1⟩