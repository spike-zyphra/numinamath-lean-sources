import Mathlib

theorem algebra_156771 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h1 : x - y^2 = 3) (h2 : x^2 + y^4 = 13) :
    x = (3 + √17) / 2 := by
  have eq1 : x = y^2 + 3 := by
    linarith
  rw [eq1] at h2
  have h3 : 2 * (y^4 + 3 * y^2 - 2) = 0 := by
    nlinarith
  have h4 : y^4 + 3 * y^2 - 2 = 0 := by
    nlinarith
  have h5 : (y^2) ^ 2 + 3 * (y^2) - 2 = 0 := by
    nlinarith [h4]
  have h6 : y^2 = (-3 + Real.sqrt 17) / 2 := by
    have h7 : (y^2) ^ 2 + 3 * (y^2) - 2 = 0 := h5
    have h8 : (y^2 - (-3 + Real.sqrt 17) / 2) * (y^2 - (-3 - Real.sqrt 17) / 2) = 0 := by
      nlinarith [h7, Real.sqrt_nonneg 17, Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)]
    cases' (mul_eq_zero.1 h8) with h9 h10
    · -- The valid solution
      linarith
    · -- The invalid solution
      have h7 : y^2 < 0 := by
        nlinarith [h10, Real.sqrt_pos.mpr (show (0 : ℝ) < 17 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)]
      nlinarith [show 0 ≤ y ^ 2 from by nlinarith]
  have eq2 : x = ((-3 + Real.sqrt 17)/2 + 3) := by
    rw [eq1]
    nlinarith [h6]
  rw [eq2]
  ring_nf
  <;> norm_num