import Mathlib

theorem algebra_4944 {a b : ℝ} (h : (a - 5) ^ 2 + abs (2 * b + 12) = 0) :
    ∑ i ∈ Finset.range 2022, abs (a + b) ^ (i + 1) = 2022 := by
  have h1 : (a - 5) ^ 2 = 0 := by
    linarith [sq_nonneg (a - 5), abs_nonneg (2 * b + 12)]
  have h2 : abs (2 * b + 12) = 0 := by
    linarith [sq_nonneg (a - 5), abs_nonneg (2 * b + 12)]
  have ha : a = 5 := by
    rw [sq_eq_zero_iff] at h1
    linarith
  have hb : b = -6 := by
    rw [abs_eq_zero] at h2
    linarith
  have hab : abs (a + b) = 1 := by
    rw [ha, hb]
    norm_num [abs_of_nonneg, abs_of_nonpos]
  rw [hab]
  norm_num