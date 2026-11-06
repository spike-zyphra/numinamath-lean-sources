import Mathlib

theorem algebra_165822 (x : ℝ) (hx : x ≠ -2) (h : 0 ≤ x) (h' : Real.sqrt x + (2 * x + 1) / (x + 2) = 2) :
    x = 1 := by
  have h1 : x ≥ 0 := by linarith
  have h2 : x + 2 ≠ 0 := by
    by_contra h3
    have h4 : x = -2 := by linarith
    contradiction
  have h_eq1 : Real.sqrt x + (2 * x + 1) / (x + 2) = 2 := h'
  have h_eq2 : Real.sqrt x * (x + 2) + (2 * x + 1) = 2 * (x + 2) := by 
    have h3 : x + 2 ≠ 0 := h2
    have h4 : Real.sqrt x + (2 * x + 1) / (x + 2) = 2 := h_eq1
    field_simp [h3] at h4 ⊢
    linarith
  have h_eq3 : Real.sqrt x * (x + 2) = 3 := by 
    nlinarith [Real.sqrt_nonneg x, Real.sq_sqrt (show 0 ≤ (x : ℝ) by linarith), sq_nonneg (x - 1), sq_nonneg (Real.sqrt x - 1), h_eq2]
  have h_eq4 : Real.sqrt x = 1 := by
    nlinarith [Real.sqrt_nonneg x, sq_nonneg (x - 1), sq_nonneg (Real.sqrt x - 1), Real.sq_sqrt (show 0 ≤ (x : ℝ) by linarith), sq_nonneg (x - 4)]
  have h_eq5 : x = 1 := by
    have h_eq6 : Real.sqrt x = 1 := h_eq4
    have h_eq7 : (Real.sqrt x) ^ 2 = (1 : ℝ) ^ 2 := by
      rw [h_eq6]
    have h_eq8 : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt (by linarith)
    nlinarith
  exact h_eq5