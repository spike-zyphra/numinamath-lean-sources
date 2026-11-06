import Mathlib

theorem algebra_187070 (x : ℝ) (hx : x ≠ 4) (h : 2 * Real.sqrt (x ^ 2 - 16) + Real.sqrt (x ^ 2 - 9) = 10 / (x - 4)) :
    x = 5 := by
  have h1 : x ^ 2 - 16 ≥ 0 := by
    by_contra h1
    push_neg at h1
    have h2 : Real.sqrt (x ^ 2 - 16) = 0 := by
      rw [Real.sqrt_eq_zero'.mpr]
      nlinarith
      all_goals nlinarith
    have h3 : Real.sqrt (x ^ 2 - 9) ≥ 0 := Real.sqrt_nonneg (x ^ 2 - 9)
    have h4 : (10 / (x - 4) ) < (0 : ℝ) := by
      have h5 : x ^ 2 < 16 := by nlinarith
      have h6 : x < 4 := by nlinarith [sq_nonneg (x + 4), sq_nonneg (x - 4)]
      have h7 : x - 4 < 0 := by nlinarith
      apply div_neg_of_pos_of_neg
      all_goals linarith
    have h5 : 2 * Real.sqrt (x ^ 2 - 16) + Real.sqrt (x ^ 2 - 9) ≥ 0 := by
      rw [h2]
      nlinarith [Real.sqrt_nonneg (x ^ 2 - 9)]
    have h6 : (10 / (x - 4) ) ≥ 0 := by
      nlinarith [h, h5]
    linarith
  have h2 : x ^ 2 - 9 ≥ 0 := by
    by_contra h2
    push_neg at h2
    have h3 : Real.sqrt (x ^ 2 - 9) = 0 := by
      rw [Real.sqrt_eq_zero'.mpr]
      nlinarith
      all_goals nlinarith
    have h4 : Real.sqrt (x ^ 2 - 16) ≥ 0 := Real.sqrt_nonneg (x ^ 2 - 16)
    have h5 : (10 / (x - 4) ) < (0 : ℝ) := by
      have h6 : x ^ 2 < 9 := by nlinarith
      have h7 : x < 3 := by nlinarith [sq_nonneg (x + 3), sq_nonneg (x - 3)]
      have h8 : x - 4 < 0 := by nlinarith
      apply div_neg_of_pos_of_neg
      all_goals linarith
    have h5 : 2 * Real.sqrt (x ^ 2 - 16) + Real.sqrt (x ^ 2 - 9) ≥ 0 := by
      rw [h3]
      nlinarith [Real.sqrt_nonneg (x ^ 2 - 16)]
    have h6 : (10 / (x - 4) ) ≥ 0 := by
      nlinarith [h, h5]
    linarith
  have h3 : x - 4 ≠ 0 := by
    intro h4
    apply hx
    linarith
  have h4 : (2 * Real.sqrt (x ^ 2 - 16) + Real.sqrt (x ^ 2 - 9)) * (x - 4) = 10 := by
    have h5 : x - 4 ≠ 0 := h3
    field_simp [(show x - 4 ≠ 0 by exact h5)] at h ⊢
    nlinarith
  have h5 : x - 4 > 0 := by
    by_contra h5
    push_neg at h5
    have h6 : (2 * Real.sqrt (x ^ 2 - 16) + Real.sqrt (x ^ 2 - 9)) * (x - 4) ≤ 0 := by
      have h7 : x - 4 ≤ 0 := by linarith
      have h8 : 2 * Real.sqrt (x ^ 2 - 16) + Real.sqrt (x ^ 2 - 9) ≥ 0 := by
        positivity
      nlinarith
    nlinarith
  have hx1 : x > 4 := by linarith
  by_cases h6 : x > 5
  · -- Assume x > 5
    have h9 : (2 * Real.sqrt (x ^ 2 - 16) + Real.sqrt (x ^ 2 - 9)) > (10 : ℝ) := by
      nlinarith [Real.sqrt_nonneg (x ^ 2 - 16), Real.sqrt_nonneg (x ^ 2 - 9),
                Real.sq_sqrt (show 0 ≤ (x ^ 2 - 16 : ℝ) by nlinarith),
                Real.sq_sqrt (show 0 ≤ (x ^ 2 - 9 : ℝ) by nlinarith),
                sq_nonneg (Real.sqrt (x ^ 2 - 16) - 3), sq_nonneg (Real.sqrt (x ^ 2 - 9) - 4),
                mul_pos (show (0 : ℝ) < x ^ 2 - 16 by nlinarith) (show (0 : ℝ) < x ^ 2 - 9 by nlinarith),
                h6
              ]
    have h10 : (2 * Real.sqrt (x ^ 2 - 16) + Real.sqrt (x ^ 2 - 9)) * (x - 4) > (10 : ℝ) := by
      have h11 : (2 * Real.sqrt (x ^ 2 - 16) + Real.sqrt (x ^ 2 - 9)) > (10 : ℝ) := h9
      have h12 : x - 4 > 0 := by linarith
      nlinarith
    nlinarith
  by_cases h8 : x < 5
  · -- Assume 4 < x < 5
    have h11 : (2 * Real.sqrt (x ^ 2 - 16) + Real.sqrt (x ^ 2 - 9)) < (10 : ℝ) := by
      nlinarith [Real.sqrt_nonneg (x ^ 2 - 16), Real.sqrt_nonneg (x ^ 2 - 9),
                Real.sq_sqrt (show 0 ≤ (x ^ 2 - 16 : ℝ) by nlinarith),
                Real.sq_sqrt (show 0 ≤ (x ^ 2 - 9 : ℝ) by nlinarith),
                sq_nonneg (Real.sqrt (x ^ 2 - 16) - 3), sq_nonneg (Real.sqrt (x ^ 2 - 9) - 4),
                mul_pos (show (0 : ℝ) < x ^ 2 - 16 by nlinarith) (show (0 : ℝ) < x ^ 2 - 9 by nlinarith)
              ]
    have h12 : (2 * Real.sqrt (x ^ 2 - 16) + Real.sqrt (x ^ 2 - 9)) * (x - 4) < (10 : ℝ) := by
      have h13 : (2 * Real.sqrt (x ^ 2 - 16) + Real.sqrt (x ^ 2 - 9)) < (10 : ℝ) := h11
      have h14 : x - 4 > 0 := by linarith
      nlinarith
    nlinarith
  · -- x = 5
    have h6 : x = 5 := by
      linarith
    exact h6