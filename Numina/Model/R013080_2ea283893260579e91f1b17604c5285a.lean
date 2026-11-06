import Mathlib


theorem algebra_304018 (b c : ℤ) (h : ∃ x1 x2 : ℝ, x1 ≠ x2 ∧ x1 > -1 ∧ x1 < 0 ∧ x2 > -1 ∧ x2 < 0 ∧
    5 * x1^2 + b * x1 + c = 0 ∧ 5 * x2^2 + b * x2 + c = 0) :
    b = 5 ∧ c = 1 := by

  rcases h with ⟨x1, x2, hx12, h11, h12, h21, h22, h31, h32⟩

  have h4 : 5 * (x1 ^ 2 - x2 ^ 2) + b * (x1 - x2) = 0 := by
    nlinarith

  have h5 : x1 - x2 ≠ 0 := by
    intro h0
    apply hx12
    linarith

  have h6 : 5 * (x1 + x2) = - (b : ℝ) := by
    apply (mul_left_inj' (show (x1 - x2 : ℝ) ≠ 0 by exact h5)).mp
    linarith

  have hb1 : b > 0 := by
    have h7 : (b : ℝ) > 0 := by
      nlinarith [show x1 + x2 > -2 by nlinarith, show x1 + x2 < (0 : ℝ) by nlinarith]
    exact_mod_cast h7

  have hb2 : b < 10 := by
    have h8 : (b : ℝ) < 10 := by
      nlinarith [show x1 + x2 > -2 by nlinarith, show x1 + x2 < (0 : ℝ) by nlinarith]
    exact_mod_cast h8

  have hc1 : c > 0 := by
    have h9 : (c : ℝ) > 0 := by
      nlinarith [sq_nonneg (x1 : ℝ), sq_nonneg (x2 : ℝ), show x1 < 0 by linarith, show x2 < 0 by linarith, show x1 > -1 by linarith, show x2 > -1 by linarith, h31, h32, h6]
    exact_mod_cast h9

  have hc2 : c < 5 := by
    have h10 : (c : ℝ) < 5 := by
      nlinarith [sq_nonneg (x1 : ℝ), sq_nonneg (x2 : ℝ), show x1 < 0 by linarith, show x2 < 0 by linarith, show x1 > -1 by linarith, show x2 > -1 by linarith, h31, h32, h6]
    exact_mod_cast h10

  have h7 : b ^ 2 > 20 * c := by
    have h8 : (b : ℝ) ^ 2 > 20 * (c : ℝ) := by
      have h13 : (x1 - x2) ^ 2 > 0 := by
        apply sq_pos_of_ne_zero
        intro h0
        apply hx12
        linarith
      nlinarith [sq_nonneg (x1 + x2 : ℝ), sq_nonneg (x1 - x2 : ℝ), h31, h32, h6]
    exact_mod_cast h8

  have h8 : b < 5 + c := by
    have h9 : 5 * (-1 : ℝ)^2 + (b : ℝ) * (-1 : ℝ) + (c : ℝ) > 0 := by
      nlinarith [sq_nonneg (x1 + 1 : ℝ), sq_nonneg (x2 + 1 : ℝ), h11, h21, h31, h32, h6]
    have h12 : (b : ℝ) < (5 + (c : ℝ) : ℝ) := by
      nlinarith
    exact_mod_cast h12

  interval_cases b <;> interval_cases c
  <;> norm_num at h7 h8 hb1 hb2 hc1 hc2
  <;> tauto