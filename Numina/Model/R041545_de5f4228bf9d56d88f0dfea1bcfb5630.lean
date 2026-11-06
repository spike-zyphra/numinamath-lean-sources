import Mathlib

theorem algebra_233817 {x : ℕ} (hx : x ≠ 0) (h1 : 60 + (0.6 * x : ℝ) = x) :
    x = 150 := by
  have eq1 : (x : ℝ) ≠ 0 := by
    exact_mod_cast show (x : ℕ) ≠ 0 by assumption
  have eq2 : (x : ℝ) = 150 := by
    norm_num at h1 
    have h2 : (x : ℝ) = 150 := by
      linarith
    exact h2
  have eq3 : x = 150 := by
    exact_mod_cast eq2
  exact eq3