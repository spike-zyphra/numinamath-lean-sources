import Mathlib

theorem algebra_12416 {n : ℤ} (h : (13 : ℝ)^ (3 * n) = (1 / 13) ^ (n - 24)) :
    n = 6 := by
  have eq1 : (1 / 13 : ℝ) ^ (n - 24) = (13 : ℝ) ^ (24 - n : ℤ) := by
    rw [show (1 / 13 : ℝ) = (13 : ℝ) ^ (-1 : ℤ) by norm_num]
    rw [← zpow_mul]
    ring_nf
    all_goals norm_num
  rw [eq1] at h
  have eq2 : (3 * n : ℤ) = (24 - n : ℤ) := by 
    have h1 : (13 : ℝ) ^ (3 * n : ℤ) = (13 : ℝ) ^ (24 - n : ℤ) := h
    have h2 : (3 * n : ℤ) = (24 - n : ℤ) := by 
      exact_mod_cast (by 
        simpa using h1
      )
    exact h2
  have eq3 : (n : ℤ) = 6 := by
    linarith
  exact_mod_cast eq3