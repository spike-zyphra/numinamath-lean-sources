import Mathlib

theorem algebra_166464 {x y : ℝ} (hx : x ≥ 0) (hy : y ≥ 0)
    (h1 : x + Real.sqrt y - 56 = 0) (h2 : Real.sqrt x + y - 56 = 0) :
    x = 49 ∧ y = 49 := by
  have eq1 : x + Real.sqrt y = 56 := by linarith
  have eq2 : Real.sqrt x + y = 56 := by linarith
  have h3 : x - y = Real.sqrt x - Real.sqrt y := by
    nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y, Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ y by linarith), h1, h2]
  have h5 : (Real.sqrt x - Real.sqrt y) * (Real.sqrt x + Real.sqrt y - 1) = 0 := by
    nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y, Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ y by linarith), h3]
  cases' (mul_eq_zero.mp h5) with h6 h7
  · -- h6 : Real.sqrt x - Real.sqrt y = 0
    have h7 : Real.sqrt x = Real.sqrt y := by linarith
    have h8 : x = y := by
      have h9 : Real.sqrt x = Real.sqrt y := by linarith
      have h10 : (Real.sqrt x) ^ 2 = (Real.sqrt y) ^ 2 := by rw [h9]
      rw [Real.sq_sqrt (show x ≥ 0 by linarith), Real.sq_sqrt (show y ≥ 0 by linarith)] at h10 
      linarith
    have eq3 : Real.sqrt x = Real.sqrt y := by linarith
    have h9 : x + Real.sqrt y = 56 := by nlinarith
    have h10 : Real.sqrt x = 7 := by
      nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y, sq_nonneg (Real.sqrt x - 7), sq_nonneg (Real.sqrt y - 7), Real.sq_sqrt (show x ≥ 0 by linarith), Real.sq_sqrt (show y ≥ 0 by linarith), h8, Real.sqrt_nonneg x]
    have hx2 : x = 49 := by
      have h11 : Real.sqrt x = 7 := h10
      rw [Real.sqrt_eq_iff_sq_eq] at h11
      · linarith
      all_goals nlinarith 
    have hy2 : y = 49 := by 
      have h11 : x = 49 := hx2
      linarith [h8, h11]
    exact ⟨hx2, hy2⟩
  · -- h7 : Real.sqrt x + Real.sqrt y - 1 = 0
    have h5 : Real.sqrt x + Real.sqrt y = 1 := by linarith
    have h6 : Real.sqrt y = 1 - Real.sqrt x := by
      linarith
    nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y, Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ y by linarith), Real.sqrt_nonneg x, Real.sqrt_nonneg x, h1, Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ y by linarith), h6]