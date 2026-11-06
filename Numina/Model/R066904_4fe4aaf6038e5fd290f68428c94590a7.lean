import Mathlib

theorem algebra_43048 {n : ℕ} (hn : n ≥ 50 + 44) (h : (50 * (30 / 100 : ℝ)) + (44 * (27 / 100 : ℝ)) = n * (50 / 100 : ℝ)) :
    n = 165 := by 
  have h1 : (n : ℝ) ≥ (50 + 44 : ℝ) := by exact_mod_cast hn
  norm_num at h
  have h4 : n ≤ 53 := by
    by_contra h4
    push_neg at h4
    have h4' : (n : ℝ) ≥ (54 : ℝ) := by exact_mod_cast h4
    nlinarith
  nlinarith