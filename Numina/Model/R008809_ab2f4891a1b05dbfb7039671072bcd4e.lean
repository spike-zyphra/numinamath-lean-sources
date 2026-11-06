import Mathlib

theorem algebra_12159 {n : ℕ} (hn : n > 0) (h : 160 + (n - 1) * 112 = 180 * n - (360 : ℝ)) :
    n = 6 := by
  have h1 : (n : ℝ) > 0 := by exact_mod_cast hn
  have eq1 : (n : ℝ) = 6 := by
    have h_eq : (160 : ℝ) + ((n : ℝ) - 1) * 112 = 180 * (n : ℝ) - 360 := by
      have h_cast : (160 + (n - 1) * 112 : ℝ) = 180 * (n : ℝ) - 360 := by
        exact_mod_cast h
      ring_nf at h_cast ⊢
      linarith
    nlinarith
  have h2 : (n : ℝ) = 6 := by 
    nlinarith
  have h3 : n = 6 := by
    exact_mod_cast h2
  exact h3