import Mathlib

theorem algebra_9665 (a : ℝ) (h : ∃ x1 x2 : ℝ, x1 ≠ x2 ∧ x1 ∈ Set.Ioo (-5) 5 ∧ x2 ∈ Set.Ioo (-5) 5 ∧
    x1^2 + 2 * a * x1 - 2 * a + 3 = 0 ∧ x2^2 + 2 * a * x2 - 2 * a + 3 = 0) :
    (-3.5 < a ∧ a < -3) ∨ (1 < a ∧ a < 2 + 1 / 3) := by

  rcases h with ⟨x1, x2, hx1x2, hx1, hx2, h1, h2⟩

  rcases hx1 with ⟨hx1l, hx1r⟩
  rcases hx2 with ⟨hx2l, hx2r⟩

  have h3 : (x1 - x2) * (x1 + x2 + 2 * a) = 0 := by
    have eq1 : x1^2 + 2 * a * x1 - 2 * a + 3 = 0 := h1
    have eq2 : x2^2 + 2 * a * x2 - 2 * a + 3 = 0 := h2
    have eq3 : x1^2 + 2 * a * x1 - 2 * a + 3 - (x2^2 + 2 * a * x2 - 2 * a + 3) = 0 := by
      linarith [eq1, eq2]
    have eq4 : x1^2 - x2^2 + 2 * a * (x1 - x2) = 0 := by 
      nlinarith [eq3]
    have eq5 : (x1 - x2) * (x1 + x2 + 2 * a) = 0 := by
      nlinarith [eq4]
    assumption

  cases (mul_eq_zero.mp h3) with
  | inl h4 =>
    have h4' : x1 = x2 := by 
      linarith
    contradiction

  | inr h4 =>
    by_cases h6 : a > 1
    · -- Suppose $a > 1$, prove $1 < a < 2 + 1 / 3$
      right
      constructor
      · -- Show 1 < a
        linarith
      · -- Show a < 2 + 1 / 3
        have h7 : 2 + 1 / 3 = (7 : ℝ) / 3 := by norm_num
        rw [h7] at *
        nlinarith [sq_pos_of_ne_zero (show (x1 - x2 : ℝ) ≠ 0 by 
          intro h'
          apply hx1x2
          linarith
        ), sq_nonneg (x1 - 5), sq_nonneg (x2 - 5), sq_nonneg (x1 + 5), sq_nonneg (x2 + 5), sq_nonneg (x1 - x2), sq_nonneg (x1 + x2 + 2 * a)]
    · -- Assume not a > 1, so a ≤ 1
      by_cases h7 : a < -3
      · -- Assume a < -3, prove -3.5 < a ∧ a < -3
        left
        constructor
        · -- Show -3.5 < a
          nlinarith [sq_pos_of_ne_zero (show (x1 - x2 : ℝ) ≠ 0 by 
            intro h'
            apply hx1x2
            linarith
          ), sq_nonneg (x1 - 5), sq_nonneg (x2 - 5), sq_nonneg (x1 + 5), sq_nonneg (x2 + 5), sq_nonneg (x1 - x2), sq_nonneg (x1 + x2 + 2 * a)]
        · -- Show a < -3
          linarith
      · -- Assume a ≥ -3
        nlinarith [sq_pos_of_ne_zero (show (x1 - x2 : ℝ) ≠ 0 by 
          intro h'
          apply hx1x2
          linarith
        ), sq_nonneg (x1 - 5), sq_nonneg (x2 - 5), sq_nonneg (x1 + 5), sq_nonneg (x2 + 5), sq_nonneg (x1 - x2), sq_nonneg (x1 + x2 + 2 * a), sq_nonneg (x1 - 5), sq_nonneg (x2 - 5), sq_nonneg (x1 + 5), sq_nonneg (x2 + 5)]