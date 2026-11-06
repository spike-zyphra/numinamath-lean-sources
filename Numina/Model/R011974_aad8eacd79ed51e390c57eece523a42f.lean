import Mathlib

open Real

theorem algebra_202522 {x : ℝ} (hx : x > 0) : x^(2 * logb 2 x) = 8 ↔
    x = 2^(Real.sqrt (3 / 2)) ∨ x = 2^(-Real.sqrt (3 / 2)) := by
  constructor
  · -- Assume x^(2 * logb 2 x) = 8, prove the disjunction of the solutions
    intro h_eq
    have h1 : 2 * (logb 2 x) ^ 2 = 3 := by
      have h2 : logb 2 (x ^ (2 * logb 2 x)) = logb 2 8 := by
        rw [h_eq]
      have h3 : logb 2 (x ^ (2 * logb 2 x)) = (2 * logb 2 x) * logb 2 x := by
        rw [logb_rpow_eq_mul_logb_of_pos]
        all_goals linarith
      have h4 : logb 2 8 = 3 := by
        rw [Real.logb_eq_iff_rpow_eq] <;> (norm_num)
      rw [h3, h4] at h2
      nlinarith
    have h2 : (logb 2 x) ^ 2 = (3 / 2 : ℝ) := by
      nlinarith
    have h3 : logb 2 x = Real.sqrt (3 / 2 : ℝ) ∨ logb 2 x = - Real.sqrt (3 / 2 : ℝ) := by
      have h4 : (logb 2 x) ^ 2 = (3 / 2 : ℝ) := h2
      have h5 : (logb 2 x - Real.sqrt (3 / 2 : ℝ)) * (logb 2 x + Real.sqrt (3 / 2 : ℝ)) = 0 := by
        nlinarith [Real.sqrt_nonneg (3 / 2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 3 / 2 by norm_num)]
      cases' (mul_eq_zero.mp h5) with h6 h7
      · -- Case where $\ln x - \sqrt{\frac{3}{2}} = 0$
        left
        linarith
      · -- Case where $\ln x + \sqrt{\frac{3}{2}} = 0$
        right
        nlinarith
    cases' h3 with h4 h5
    · -- Case $\ln x = \sqrt{\frac{3}{2}}$
      have h6 : x = (2 : ℝ) ^ (Real.sqrt (3 / 2 : ℝ)) := by
        have h7 : logb 2 x = Real.sqrt (3 / 2 : ℝ) := h4
        rw [← h7]
        field_simp
      left
      tauto
    · -- Case $\ln x = -\sqrt{\frac{3}{2}}$
      have h8 : x = (2 : ℝ) ^ (-Real.sqrt (3 / 2 : ℝ)) := by
        have h9 : logb 2 x = -Real.sqrt (3 / 2 : ℝ) := h5
        rw [← h9]
        field_simp
      right
      tauto
  · -- Assume x is either of the solutions, prove x^(2 * logb 2 x) = 8
    rintro (h_eq | h_eq)
    · -- Case x = 2^(Real.sqrt (3 / 2))
      rw [h_eq]
      have h7 : logb 2 ((2 : ℝ) ^ (Real.sqrt (3 / 2 : ℝ))) = Real.sqrt (3 / 2 : ℝ) := by
        rw [logb_rpow_eq_mul_logb_of_pos]
        all_goals
          norm_num
      rw [h7]
      have h8 : ( (2 : ℝ) ^ (Real.sqrt (3 / 2 : ℝ)) ) ^ (2 * (Real.sqrt (3 / 2 : ℝ)) ) = (2 : ℝ) ^ (2 * (Real.sqrt (3 / 2 : ℝ)) * (Real.sqrt (3 / 2 : ℝ)) ) := by
          rw [← Real.rpow_mul]
          ring_nf
          all_goals
            positivity
      have h9 : (2 * (Real.sqrt (3 / 2 : ℝ)) * (Real.sqrt (3 / 2 : ℝ)) ) = (3 : ℝ) := by
          nlinarith [Real.sqrt_nonneg (3 / 2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 3 / 2 by norm_num)]
      have h10 : (2 : ℝ) ^ (2 * (Real.sqrt (3 / 2 : ℝ)) * (Real.sqrt (3 / 2 : ℝ)) ) = (8 : ℝ) := by
          rw [h9]
          norm_num
      rw [h8, h10]
    · -- Case x = 2^(-Real.sqrt (3 / 2))
      rw [h_eq]
      have h7 : logb 2 ((2 : ℝ) ^ (-Real.sqrt (3 / 2 : ℝ)) ) = -Real.sqrt (3 / 2 : ℝ) := by
        rw [logb_rpow_eq_mul_logb_of_pos]
        all_goals
          norm_num
      rw [h7]
      have h8 : ( (2 : ℝ) ^ (-Real.sqrt (3 / 2 : ℝ)) ) ^ (2 * (-Real.sqrt (3 / 2 : ℝ)) ) = (2 : ℝ) ^ (2 * (-Real.sqrt (3 / 2 : ℝ)) * (-Real.sqrt (3 / 2 : ℝ)) ) := by
          rw [← Real.rpow_mul]
          ring_nf
          all_goals
            positivity
      have h9 : (2 * (-Real.sqrt (3 / 2 : ℝ)) * (-Real.sqrt (3 / 2 : ℝ)) ) = (3 : ℝ) := by
          nlinarith [Real.sqrt_nonneg (3 / 2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 3 / 2 by norm_num)]
      have h10 : (2 : ℝ) ^ (2 * (-Real.sqrt (3 / 2 : ℝ)) * (-Real.sqrt (3 / 2 : ℝ)) ) = (8 : ℝ) := by
          rw [h9]
          norm_num
      rw [h8, h10]