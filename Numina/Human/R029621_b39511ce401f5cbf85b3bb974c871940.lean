import Mathlib

theorem inequalities_129768 (a b c : ℝ) (h : a^2 + b^2 + c^2 = 1) :
    -1/2 ≤ a*b + b*c + c*a ∧ a*b + b*c + c*a ≤ 1 := by

  have h1 : a * b + b * c + c * a ≥ -1 / 2 := by 
    have h_sum_sq : (a + b + c) ^ 2 ≥ 0 := by 
      exact sq_nonneg (a + b + c)
    have h_expand : (a + b + c) ^ 2 = a^2 + b^2 + c^2 + 2 * (a * b + b * c + c * a) := by 
      ring
    rw [h] at h_expand
    linarith

  have h2 : a * b + b * c + c * a ≤ 1 := by
    have h_sum_sq : a^2 + b^2 + c^2 ≥ a * b + b * c + c * a := by
      have h1 : 0 ≤ (a - b) ^ 2 := by 
        exact sq_nonneg (a - b)
      have h2 : 0 ≤ (b - c) ^ 2 := by 
        exact sq_nonneg (b - c)
      have h3 : 0 ≤ (c - a) ^ 2 := by 
        exact sq_nonneg (c - a)
      have h_sum : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 ≥ 0 := by 
        linarith [h1, h2, h3]
      linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
    linarith [h, h_sum_sq]

  exact ⟨h1, h2⟩