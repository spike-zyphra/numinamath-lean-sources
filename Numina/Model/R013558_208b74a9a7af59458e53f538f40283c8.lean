import Mathlib

theorem inequalities_192359 (d : ℤ) (h : d < 7 * Real.sqrt (0.9) ∧ 7 * Real.sqrt (0.9) < d + 1) :
    d = 6 := by
  have h1 : d < 7 * Real.sqrt (0.9) := h.1
  have h2 : 7 * Real.sqrt (0.9) < d + 1 := h.2
  have h3 : Real.sqrt (0.9 : ℝ) ^ 2 = 0.9 := by
    rw [Real.sq_sqrt]
    norm_num
  have h4 : Real.sqrt (0.9 : ℝ) > 0.9 := by
    nlinarith [Real.sqrt_nonneg (0.9 : ℝ), Real.sq_sqrt (show (0.9 : ℝ) ≥ 0 by norm_num), sq_nonneg (Real.sqrt (0.9 : ℝ) - 0.9)]
  have h5 : Real.sqrt (0.9 : ℝ) < 0.95 := by
    nlinarith [Real.sqrt_nonneg (0.9 : ℝ), Real.sq_sqrt (show (0.9 : ℝ) ≥ 0 by norm_num), sq_nonneg (Real.sqrt (0.9 : ℝ) - 0.95)]
  have h6 : (d : ℝ) < 7 * Real.sqrt (0.9 : ℝ) := by
    exact_mod_cast h1
  have h7 : 7 * Real.sqrt (0.9 : ℝ) < (d + 1 : ℝ) := by
    exact_mod_cast h2
  have h8 : (d : ℝ) < 6.65 := by
    nlinarith [h6, h5]
  have h9 : (d : ℝ) > 5.3 := by
    nlinarith [h7, h4]
  have h10 : d ≤ 6 := by
    by_contra h11
    push_neg at h11
    have h11' : d ≥ 7 := by
      omega
    have h12 : (d : ℝ) ≥ 7 := by
      exact_mod_cast h11'
    nlinarith
  have h13 : d ≥ 6 := by
    by_contra h14
    push_neg at h14
    have h14' : d ≤ 5 := by
      omega
    have h15 : (d : ℝ) ≤ 5 := by
      exact_mod_cast h14'
    nlinarith
  have h14 : d = 6 := by
    linarith
  exact h14