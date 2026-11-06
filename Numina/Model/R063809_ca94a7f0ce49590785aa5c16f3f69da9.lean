import Mathlib

theorem algebra_320465 {x : ℝ} (hx : x = 2 - Real.sqrt 3) :
    (x^4 - 4 * x^3 - x^2 + 9 * x - 4) / (x^2 - 4 * x + 5) = -Real.sqrt 3 / 4 := by
  have h1 : x = 2 - Real.sqrt 3 := hx
  -- Let's compute the denominator: x^2 - 4 x + 5
  have h2 : x^2 - 4 * x + 4 = 3 := by
    rw [h1]
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have h3 : x^2 - 4 * x + 5 = 4 := by
    nlinarith
  have h5 : x^4 - 4 * x^3 - x^2 + 9 * x - 4 = -Real.sqrt 3 := by
    rw [h1]
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
    Real.sqrt_nonneg 3]
  rw [h3, h5]
  <;> ring_nf <;> field_simp <;> ring_nf <;> norm_num