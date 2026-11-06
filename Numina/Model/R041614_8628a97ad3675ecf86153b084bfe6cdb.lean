import Mathlib

open Real

theorem inequalities_276949 (k : ℝ) (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : k * a * b * c / (a + b + c) ≥ (a + b)^2 + (a + b + 4 * c)^2) :
    k ≥ 100 := by
  have h1 : a + b + c > 0 := by
    linarith
  have h2 : k * a * b * c ≥ (a + b)^2 * (a + b + c) + (a + b + 4 * c)^2 * (a + b + c) := by
    have h3 : (a + b + c) > 0 := h1
    have h4 : k * a * b * c / (a + b + c) ≥ (a + b)^2 + (a + b + 4 * c)^2 := by linarith [h]
    have h5 : k * a * b * c ≥ ((a + b)^2 + (a + b + 4 * c)^2) * (a + b + c) := by
      have h7 : 0 < (a + b + c) := h1
      apply (le_div_iff₀ h7).mp at h4
      linarith
    nlinarith
  by_contra h3
  push_neg at h3
  have h4 : k * a * b * c < 100 * a * b * c := by
    have h5 : a * b * c > 0 := by
      apply mul_pos
      apply mul_pos
      exact ha
      exact hb
      exact hc
    have h6 : k - 100 < 0 := by linarith
    have h7 : (k - 100) * (a * b * c) < 0 := by
      apply mul_neg_of_neg_of_pos
      exact h6
      linarith [h5]
    linarith [h7]
  have h5 : k * a * b * c ≥ 100 * a * b * c := by
    nlinarith [ sq_nonneg (a - b), sq_nonneg (a - 2 * c), sq_nonneg (b - 2 * c), 
        sq_nonneg (a + b - 2 * c), sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a + b - 4 * c), 
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc 
    ]
  linarith [h4, h5]