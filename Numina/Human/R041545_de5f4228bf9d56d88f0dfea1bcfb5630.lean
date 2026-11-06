import Mathlib

theorem algebra_233817 {x : ℕ} (hx : x ≠ 0) (h1 : 60 + (0.6 * x : ℝ) = x) :
    x = 150 := by
  have h2 : (x : ℝ) = 150 := by
    have h1' : (x : ℝ) = 150 := by
      norm_num at h1 ⊢
      linarith
    exact h1'
  have h3 : x = 150 := by
    exact_mod_cast h2
  exact h3