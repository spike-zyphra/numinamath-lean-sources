import Mathlib

theorem algebra_14585 (n : ℕ) : (2 ^ (n + 4) - 2 * (2 ^ n)) / (2 * (2 ^ (n + 3))) = (7 / 8: ℝ) := by
  have eq1 : ((2 ^ (n + 4) - 2 * (2 ^ n) : ℝ) ) = (14 * (2 ^ n : ℝ) ) := by
    ring_nf
  have eq2 : ((2 * (2 ^ (n + 3)) : ℝ) ) = (16 * (2 ^ n : ℝ) ) := by
    ring_nf
  rw [eq1, eq2]
  have h4 : (2 ^ n : ℝ) ≠ 0 := by
    have h5 : (2 ^ n : ℝ) > (0 : ℝ) := by positivity
    linarith
  field_simp [h4]
  <;> ring_nf <;> norm_num