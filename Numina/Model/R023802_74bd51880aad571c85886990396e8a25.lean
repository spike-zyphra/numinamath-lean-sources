import Mathlib

open Real

theorem algebra_1449 (x : ℝ) : (x + 1).sqrt + x = 0 ↔
    x = (1 - sqrt 5) / 2 := by
  constructor
  · -- Assume (x + 1).sqrt + x = 0, prove x = (1 - Real.sqrt 5) / 2
    intro h
    have h1 : (x + 1).sqrt = -x := by linarith
    have h2 : 0 ≤ (x + 1).sqrt := by
      apply Real.sqrt_nonneg
    have h3 : x ≤ 0 := by
      have h4 : (x + 1).sqrt = -x := h1
      have h5 : 0 ≤ -x := by
        linarith [h4, h2]
      linarith
    have h4 : ((x + 1).sqrt) ^ 2 = (-x) ^ 2 := by
      rw [h1]
    have h_nonneg : 0 ≤ x + 1 := by
      by_contra h_neg
      push_neg at h_neg
      have h8 : (x + 1).sqrt = 0 := by
        rw [Real.sqrt_eq_zero']
        all_goals nlinarith
      have h10 : -x = 0 := by
        linarith [h8, h1]
      have h11 : x = 0 := by linarith [h10]
      nlinarith [h11]
    have h5 : ((x + 1).sqrt) ^ 2 = x + 1 := Real.sq_sqrt (show (0 : ℝ) ≤ x + 1 by linarith)
    have h9 : x + 1 = x ^ 2 := by
      nlinarith [h4, h5]
    have h10 : x ^ 2 - x - 1 = 0 := by
      linarith [h9]
    have h11 : x ^ 2 - x - 1 = 0 := h10
    have h13 : (x - (1 + Real.sqrt 5) / 2) * (x - (1 - Real.sqrt 5) / 2) = 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), h11]
    cases' (mul_eq_zero.1 h13) with h14 h15
    · -- Case 1: x = (1 + Real.sqrt 5) / 2
      have h16 : x = (1 + Real.sqrt 5) / 2 := by
        linarith
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), h16]
    · -- Case 2: x = (1 - Real.sqrt 5) / 2
      linarith
  · -- Assume x = (1 - Real.sqrt 5) / 2, prove (x + 1).sqrt + x = 0
    intro h
    have h1 : x = (1 - Real.sqrt 5) / 2 := by
      linarith
    have h2 : x + 1 = (3 - Real.sqrt 5) / 2 := by
      nlinarith [h1, Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num)]
    have h3 : (x + 1).sqrt = (Real.sqrt 5 - 1) / 2 := by
      have h4 : (x + 1).sqrt = Real.sqrt ((3 - Real.sqrt 5) / 2) := by
        rw [h2]
      rw [h4]
      have h5 : ((Real.sqrt 5 - 1) / 2) ^ 2 = (3 - Real.sqrt 5) / 2 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
      have h7 : 0 ≤ (Real.sqrt 5 - 1) / 2 := by
        have h8 : 1 < Real.sqrt 5 := Real.lt_sqrt_of_sq_lt (by norm_num)
        linarith
      have h6 : Real.sqrt ((3 - Real.sqrt 5) / 2) = (Real.sqrt 5 - 1) / 2 := by
        rw [←h5]
        field_simp
      linarith [h6]
    rw [h3]
    nlinarith [h1, Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num)]