import Mathlib

theorem inequalities_253257 (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    |(a + Real.sqrt (a^2 + 2 * b^2)) / (2 * b)| < 1 ∨ |(a - Real.sqrt (a^2 + 2 * b^2)) / (2 * b)| < 1 := by
  by_contra h
  push_neg at h
  have h1 : |(a + Real.sqrt (a^2 + 2 * b^2)) / (2 * b)| ≥ 1 := by linarith [h.left]
  have h2 : |(a - Real.sqrt (a^2 + 2 * b^2)) / (2 * b)| ≥ 1 := by linarith [h.right]
  have h3 : |(a + Real.sqrt (a^2 + 2 * b^2)) / (2 * b)| * |(a - Real.sqrt (a^2 + 2 * b^2)) / (2 * b)| = (1 / 2 : ℝ) := by
    have h4 : |(a + Real.sqrt (a^2 + 2 * b^2)) / (2 * b)| * |(a - Real.sqrt (a^2 + 2 * b^2)) / (2 * b)| =
        |((a + Real.sqrt (a^2 + 2 * b^2)) / (2 * b)) * ((a - Real.sqrt (a^2 + 2 * b^2)) / (2 * b))| := by
      rw [abs_mul]
    rw [h4]
    have h5 : ((a + Real.sqrt (a^2 + 2 * b^2)) / (2 * b)) * ((a - Real.sqrt (a^2 + 2 * b^2)) / (2 * b)) = (- (1 / 2) : ℝ) := by
      field_simp [hb]
      nlinarith [Real.sqrt_nonneg (a^2 + 2 * b^2), Real.sq_sqrt (show (0 : ℝ) ≤ a^2 + 2 * b^2 by positivity)]
    rw [h5]
    norm_num [abs_of_nonneg]
  have h4 : |(a + Real.sqrt (a^2 + 2 * b^2)) / (2 * b)| * |(a - Real.sqrt (a^2 + 2 * b^2)) / (2 * b)| < 1 := by
    nlinarith [h3]
  nlinarith [h1, h2, h4]