import Mathlib

theorem algebra_284029 (x : ℝ) (hx : 0 < x) :
    (2 * x ^ 3 - x ^ 2 - x + 1) ^ (1 + 1 / (2 * x + 1)) = 1 ↔ x = 1 := by
  constructor
  · -- Assume (2 * x ^ 3 - x ^ 2 - x + 1) ^ (1 + 1 / (2 * x + 1)) = 1, prove x = 1
    intro h_eq
    have h1 : 2 * x ^ 3 - x ^ 2 - x + 1 > 0 := by
      nlinarith [sq_pos_of_pos hx, sq_nonneg (x - 1), sq_nonneg (x), sq_nonneg (x + 1)]
    have h2 : 1 + (1 / (2 * x + 1)) > 0 := by
      have h3 : 2 * x + 1 > 0 := by 
        linarith
      positivity
    have h3 : 2 * x ^ 3 - x ^ 2 - x + 1 = 1 := by
      have h4 : (2 * x ^ 3 - x ^ 2 - x + 1) ^ (1 + 1 / (2 * x + 1)) = 1 := h_eq
      have h5 : Real.log ((2 * x ^ 3 - x ^ 2 - x + 1) ^ (1 + 1 / (2 * x + 1))) = Real.log (1 : ℝ) := by
        rw [h4]
      have h8 : Real.log ((2 * x ^ 3 - x ^ 2 - x + 1) ^ (1 + 1 / (2 * x + 1))) = (1 + 1 / (2 * x + 1)) * Real.log (2 * x ^ 3 - x ^ 2 - x + 1) := by
        rw [Real.log_rpow]
        all_goals nlinarith
      rw [h8] at h5
      have h9 : Real.log (1 : ℝ) = (0 : ℝ) := by
        norm_num
      rw [h9] at h5
      have h10 : (1 + 1 / (2 * x + 1)) ≠ 0 := by
        have h3 : 2 * x + 1 > 0 := by 
          linarith
        have h11 : 1 / (2 * x + 1) > 0 := by positivity
        linarith
      have h11 : Real.log (2 * x ^ 3 - x ^ 2 - x + 1) = 0 := by 
        apply (mul_right_inj' h10).mp
        linarith
      have h12 : 2 * x ^ 3 - x ^ 2 - x + 1 = 1 := by 
        have h15 : Real.log (2 * x ^ 3 - x ^ 2 - x + 1) = 0 := h11
        have h16 : 2 * x ^ 3 - x ^ 2 - x + 1 > 0 := h1
        have h17 : 2 * x ^ 3 - x ^ 2 - x + 1 = Real.exp (Real.log (2 * x ^ 3 - x ^ 2 - x + 1)) := by 
          rw [Real.exp_log]
          all_goals nlinarith
        rw [h15] at h17
        have h18 : Real.exp (0 : ℝ) = (1 : ℝ) := by 
          norm_num
        rw [h18] at h17
        linarith
      linarith
    -- Solving 2 * x ^ 3 - x ^ 2 - x + 1 = 1
    have h4 : 2 * x ^ 3 - x ^ 2 - x + 1 = 1 := by
      linarith [h3]
    have h5 : x * (2 * x ^ 2 - x - 1) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h5) with h6 h7
    · -- Case where $x = 0$.
      nlinarith
    · -- Case where $2x^2 - x - 1 = 0$.
      have h8 : 2 * x^ 2 - x - 1 = 0 := by
        linarith
      have h9 : (x - 1) * (2 * x + 1) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h9) with h10 h11
      · -- Case where $x -1 =0$.
        linarith
      · -- Case where $2x +1 =0$.
        nlinarith
  · -- Assume x=1.
    intro h_eq
    rw [h_eq]
    norm_num