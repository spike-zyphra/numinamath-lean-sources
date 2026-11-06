import Mathlib

theorem algebra_254105 {a b c : ℝ} (h : ¬(a = 0 ∧ b = 0 ∧ c = 0)) :
    (a + b + c)^2 - 8 * a * b > 0 ∨ (a + b + c)^2 - 8 * b * c > 0 ∨
    (a + b + c)^2 - 8 * c * a > 0 := by

  by_contra h1
  push_neg at h1

  have h2 : (a + b + c) ^ 2 - 8 * a * b ≤ 0 := by
    linarith

  have h3 : (a + b + c) ^ 2 - 8 * b * c ≤ 0 := by 
    linarith

  have h4 : (a + b + c) ^ 2 - 8 * c * a ≤ 0 := by 
    linarith

  -- Summing the inequalities
  have h5 : 3 * (a + b + c) ^ 2 ≤ 8 * (a * b + b * c + c * a) := by 
    nlinarith [h2, h3, h4]

  by_cases h6 : a + b + c = 0
  · -- Case a + b + c = 0
    have hc : c = - (a + b) := by linarith 
    rw [hc] at h5 
    have h7 : a * b + b * (- (a + b)) + (- (a + b)) * a = - (a ^ 2 + a * b + b ^ 2) := by 
      ring 
    -- Substitute `c` in the `ab + bc + ca` term
    have h8 : a ^ 2 + a * b + b ^ 2 > 0 := by 
      by_contra h8
      push_neg at h8
      have h9 : a ^ 2 + a * b + b ^ 2 ≥ 0 := by 
        nlinarith [sq_nonneg (a + b / 2), sq_nonneg (b + a / 2), sq_nonneg (a - b)]
      have h10 : a ^ 2 + a * b + b ^ 2 = 0 := by 
        linarith
      have h11 : a = 0 := by 
        nlinarith [sq_nonneg (a + b / 2), sq_nonneg (b + a / 2), sq_nonneg (a - b), h10]
      have h12 : b = 0 := by 
        nlinarith [sq_nonneg (a + b / 2), sq_nonneg (b + a / 2), sq_nonneg (a - b), h10]
      have h13 : c = 0 := by 
        rw [hc] 
        linarith 
      have h14 : a = 0 ∧ b = 0 ∧ c = 0 := by 
        constructor
        · exact h11 
        constructor
        · exact h12 
        · exact h13 
      contradiction 
    nlinarith [sq_nonneg (a + b), sq_nonneg (a - b), sq_nonneg (a), sq_nonneg (b), h8]
  · -- Case a + b + c ≠ 0
    have h8 : (a + b + c) ^ 2 > 0 := by 
      have hne : a + b + c ≠ 0 := h6
      have h9 : (a + b + c) ^ 2 > 0 := by 
        apply pow_two_pos_of_ne_zero 
        exact hne 
      linarith 
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a + b + c), sq_nonneg (a - b + c), sq_nonneg (a + b - c), sq_nonneg (-a + b + c)]