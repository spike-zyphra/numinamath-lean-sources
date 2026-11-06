import Mathlib

theorem algebra_153045 {n : ℕ} (hn : n > 0) (h : (1 - 0.25 : ℝ) * n = 0.02 * (1 - 0.25 : ℝ) * n) :
    n = 4107 := by 
  have h1 : (n : ℝ) > 0 := by 
    exact_mod_cast hn
  have eq1 : (n : ℝ) = 0 := by
    ring_nf at h 
    have : (n : ℝ) = 0 := by 
      nlinarith 
    exact this 
  have h2 : (n : ℝ) > 0 := h1 
  have h3 : (n : ℝ) = 0 := eq1
  have h4 : (n : ℝ) > 0 := h1 
  have h5 : (n : ℝ) = 0 := h3 
  linarith