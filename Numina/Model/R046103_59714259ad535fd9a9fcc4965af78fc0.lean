import Mathlib

theorem algebra_301514 (k : ℝ) (x : ℝ) (hx : x^4 - 2 * k * x^2 + k^2 + 2 * k - 3 = 0) :
    -Real.sqrt 2 ≤ x ∧ x ≤ Real.sqrt 2 := by
  have h1 : (x^2 - k)^2 = 3 - 2 * k := by
    nlinarith
  have h2 : 3 - 2 * k ≥ 0 := by
    nlinarith [sq_nonneg (x^2 - k)]
  have h3 : x ^ 2 ≤ 2 := by
    nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (k - 1), sq_nonneg (x ^ 2 - k), sq_nonneg (x ^ 2 - 1), sq_nonneg (k - 1)]
  have h4 : -Real.sqrt 2 ≤ x := by
    have h5 : x ^ 2 ≤ (2 : ℝ) := h3
    have h6 : -Real.sqrt 2 ≤ x := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg x]
    exact h6
  have h7 : x ≤ Real.sqrt 2 := by
    have h5 : x ^ 2 ≤ (2 : ℝ) := h3
    have h8 : x ≤ Real.sqrt 2 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg x]
    exact h8
  exact ⟨h4, h7⟩