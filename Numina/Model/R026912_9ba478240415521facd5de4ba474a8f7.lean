import Mathlib

theorem algebra_153505 (x : ℝ) : 5 * 5^(2 * x) - 6 * 5^x + 1 = (0 : ℝ) ↔ x = -1 ∨ x = 0 := by
  constructor
  · -- Assume the equation holds, prove x = -1 ∨ x = 0
    intro h_eq
    have h1 : (5 : ℝ) ^ (2 * x) = ((5 : ℝ) ^ x) ^ 2 := by
      calc
        (5 : ℝ) ^ (2 * x) = (5 : ℝ) ^ (2 * x : ℝ) := by rfl
        _ = ((5 : ℝ) ^ (x : ℝ)) ^ 2 := by
          rw [← Real.rpow_natCast]
          rw [← Real.rpow_mul]
          ring_nf
          all_goals norm_num
          all_goals linarith
        _ = ((5 : ℝ) ^ x) ^ 2 := by ring
    rw [h1] at h_eq
    have h2 : 5 * ((5 : ℝ) ^ x) ^ 2 - 6 * ((5 : ℝ) ^ x) + 1 = (0 : ℝ) := by
      nlinarith
    have h3 : (5 * ((5 : ℝ) ^ x) - (1 : ℝ)) * ((5 : ℝ) ^ x - (1 : ℝ)) = (0 : ℝ) := by
      nlinarith
    cases' (mul_eq_zero.mp h3) with h4 h5
    · -- Case 5 * 5^x - 1 = 0
      have h6 : (5 : ℝ) ^ x = (1 / 5 : ℝ) := by
        linarith
      have h7 : x = (-1 : ℝ) := by
        have h8 : (5 : ℝ) ^ x = (1 / 5 : ℝ) := h6
        have h9 : (5 : ℝ) ^ (-1 : ℝ) = (1 / 5 : ℝ) := by
          norm_num
        have h10 : x = (-1 : ℝ) := by
          apply_fun (Real.logb (5 : ℝ)) at h8
          have h11 : Real.logb (5 : ℝ) ((5 : ℝ) ^ x) = x := by
            rw [Real.logb_rpow]
            all_goals norm_num
          have h12 : Real.logb (5 : ℝ) ((1 / 5 : ℝ)) = (-1 : ℝ) := by
            rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
          rw [h11] at h8
          linarith [h12, h8]
        exact h10
      left
      exact h7
    · -- Case 5^x - 1 = 0
      have h6 : (5 : ℝ) ^ x = (1 : ℝ) := by
        linarith
      have h7 : x = (0 : ℝ) := by
        have h8 : (5 : ℝ) ^ x = (1 : ℝ) := h6
        have h9 : (5 : ℝ) ^ (0 : ℝ) = (1 : ℝ) := by
          norm_num
        have h10 : x = (0 : ℝ) := by
          apply_fun (Real.logb (5 : ℝ)) at h8
          have h11 : Real.logb (5 : ℝ) ((5 : ℝ) ^ x) = x := by
            rw [Real.logb_rpow]
            all_goals norm_num
          have h12 : Real.logb (5 : ℝ) (1 : ℝ) = (0 : ℝ) := by
            simp [Real.logb_one]
          rw [h11] at h8
          linarith [h12, h8]
        exact h10
      right
      exact h7
  · -- Assume x = -1 ∨ x = 0, prove 5 * 5^(2 * x) - 6 * 5^x + 1 = (0 : ℝ)
    rintro (h_eq | h_eq)
    · -- Case x = -1
      rw [show x = (-1 : ℝ) by linarith]
      norm_num
    · -- Case x = 0
      rw [show x = (0 : ℝ) by linarith]
      norm_num