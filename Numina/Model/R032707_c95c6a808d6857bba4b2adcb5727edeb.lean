import Mathlib


theorem algebra_167288 (x : ℝ) :
    |x - 2|^(10 * x^2 - 3 * x - 1) = 1 ↔
    x = -1 / 5 ∨ x = 1 / 2 ∨ x = 1 ∨ x = 3 := by 
  constructor
  · -- Assume |x-2|^(10x^2-3x-1) = 1, prove x ∈ {-1/5, 1/2, 1, 3}
    intro h_eq
    have h1 : |x - 2|^(10 * x^2 - 3 * x - 1) = 1 := h_eq
    have h2 : (10 * x^2 - 3 * x - 1) = (0 : ℝ) ∨ |x - 2| = (1 : ℝ) := by
      by_cases h3 : |x - 2| > 0
      · -- |x - 2| > 0
        have h4 : |x - 2| ^ (10 * x ^ 2 - 3 * x - 1) = 1 := h1
        have h5 : (10 * x^2 - 3 * x - 1) * (Real.log (|x - 2|)) = 0 := by
          have h6 : Real.log (|x - 2| ^ (10 * x ^ 2 - 3 * x - 1)) = Real.log (1 : ℝ) := by
            rw [h4]
          have h7 : Real.log (|x - 2| ^ (10 * x ^ 2 - 3 * x - 1)) = (10 * x ^ 2 - 3 * x - 1) * Real.log (|x - 2|) := by
            rw [Real.log_rpow]
            all_goals
              try linarith [abs_nonneg (x - 2)]
          rw [h7] at h6
          have h8 : Real.log (1 : ℝ) = 0 := Real.log_one
          rw [h8] at h6
          linarith
        cases (mul_eq_zero.mp h5) with
        | inl h8 =>
          left
          linarith
        | inr h9 =>
          right
          have h10 : |x - 2| = 1 := by
            have h11 : Real.log (|x - 2|) = 0 := by
              linarith
            have h12 : |x - 2| = 1 := by
              rw [Real.log_eq_zero] at h11
              rcases h11 with (r | r | r)
              · linarith
              · linarith
              · linarith
            linarith
          linarith
      · -- |x - 2| = 0
        have h0 : |x - 2| = 0 := by
          linarith [abs_nonneg (x - 2), h3]
        have h39 : x = 2 := by
          rw [abs_eq_zero] at h0
          linarith
        rw [h39] at h1
        norm_num at h1
    cases h2 with
    | inl h_eq0 =>
      have h3 : 10 * x^2 - 3 * x - 1 = 0 := by linarith
      have h7 : (x + 1 / 5) * (x - 1 / 2) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h7) with h8 h9
      · -- x + 1/5 = 0
        left
        linarith
      · -- x - 1/2 = 0
        right
        left
        linarith
    | inr h3 =>
      have h3' : |x - 2| = 1 := by
        linarith
      cases eq_or_eq_neg_of_abs_eq h3' with
      | inl h4 =>
        right
        right
        right
        linarith
      | inr h4 =>
        right
        right
        left
        linarith
  · -- Assume x ∈ {-1/5, 1/2, 1, 3}, prove |x-2|^(10x^2-3x-1) = 1
    rintro (h_eq | h_eq | h_eq | h_eq)
    · -- x = -1/5
      rw [h_eq]
      norm_num [Real.rpow_zero]
    · -- x = 1/2
      rw [h_eq]
      norm_num [Real.rpow_zero]
    · -- x = 1
      rw [h_eq]
      norm_num
    · -- x = 3
      rw [h_eq]
      norm_num