import Mathlib

theorem algebra_10832 {n : ℕ} (hn : n = 6) :
    (2 * Real.sqrt (n ^ 2 + 8 ^ 2)) = 20 := by
  have h1 : (n : ℝ) = 6 := by
    exact_mod_cast hn
  rw [show (n : ℝ) = (6 : ℝ) by simpa using h1]
  have h2 : Real.sqrt ((6 : ℝ) ^ 2 + (8 : ℝ) ^ 2) = (10 : ℝ) := by 
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  rw [h2]
  all_goals norm_num