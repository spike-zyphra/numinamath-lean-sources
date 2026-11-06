import Mathlib

open Real

theorem algebra_316791 {n : ℕ} (hn : n > 2) :
    logb (n - 1) (n - 1) = logb n (n - 1 + 1) := by
  have h1 : (n : ℝ) > (2 : ℝ) := by
    exact_mod_cast (show n > 2 by linarith)
  have h2 : (n - 1 : ℝ) > 1 := by
    have h3 : n > 2 := hn
    have h4 : n ≥ 3 := by linarith
    have h5 : (n : ℝ) ≥ (3 : ℝ) := by exact_mod_cast h4
    have h6 : (n - 1 : ℝ) ≥ (2 : ℝ) := by
      have : (n - 1 : ℝ) = (n : ℝ) - 1 := by
        ring_nf
      linarith
    linarith
  have h3 : logb (n - 1) (n - 1) = 1 := by
    rw [logb_eq_iff_rpow_eq] <;> (try norm_num)
    all_goals linarith
  have h4 : logb n (n - 1 + 1) = 1 := by
    have h5 : (n - 1 + 1 : ℝ) = (n : ℝ) := by
      have h8 : (n - 1 + 1 : ℝ) = (n : ℝ) := by
        simp
      exact_mod_cast h8
    rw [h5]
    have h6 : logb n (n : ℝ) = 1 := by
      rw [logb_eq_iff_rpow_eq] <;> (try norm_num)
      all_goals linarith
    linarith
  linarith [h3, h4]