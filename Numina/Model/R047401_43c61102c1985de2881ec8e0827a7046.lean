import Mathlib

theorem algebra_216811 (x : ℝ) :
    Real.sqrt (|x - 1| + |x + 4|) = |x| ↔ x = -Real.sqrt 5 ∨ x = 3 := by
  constructor
  · -- Assume √(|x - 1| + |x + 4|) = |x|, prove x = -√5 ∨ x = 3
    intro h
    have h1 : |x - 1| + |x + 4| ≥ 0 := by
      cases' abs_cases (x - 1) with h1 h1 <;> cases' abs_cases (x + 4) with h2 h2 <;> linarith
    have h2 : (|x - 1| + |x + 4|) = |x| ^ 2 := by
      calc
        |x - 1| + |x + 4| = (Real.sqrt (|x - 1| + |x + 4|)) ^ 2 := by
          rw [Real.sq_sqrt]
          linarith [abs_nonneg (x - 1), abs_nonneg (x + 4)]
        _ = |x| ^ 2 := by
          rw [h]
    by_cases h3 : x ≥ 1
    · -- x ≥ 1
      rw [abs_of_nonneg (by linarith : x - 1 ≥ 0), abs_of_nonneg (by linarith : x + 4 ≥ 0), abs_of_nonneg (by linarith : x ≥ 0)] at h2
      have h3 : (x - 3) * (x + 1) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 h3) with h4 h4
      · -- x - 3 = 0, so x = 3
        right
        linarith
      · -- x + 1 = 0, x = -1, which contradicts x ≥ 1
        linarith
    by_cases h4 : x ≥ -4
    · -- -4 ≤ x < 1
      by_cases h5 : x ≥ 0
      · -- 0 ≤ x < 1
        rw [abs_of_nonpos (by linarith : x - 1 ≤ 0), abs_of_nonneg (by linarith : x + 4 ≥ 0), abs_of_nonneg (by linarith : x ≥ 0)] at h2
        nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num), Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num)]
      · -- -4 ≤ x < 0
        rw [abs_of_nonpos (by linarith : x - 1 ≤ 0), abs_of_nonneg (by linarith : x + 4 ≥ 0), abs_of_nonpos (by linarith : x ≤ 0)] at h2
        have h2a : x ^ 2 = 5 := by
          nlinarith
        have h3a : x = Real.sqrt 5 ∨ x = -Real.sqrt 5 := by
          apply eq_or_eq_neg_of_sq_eq_sq
          field_simp
          linarith
        cases' h3a with h4a h4a
        · -- x = Real.sqrt 5, which contradicts x < 0
          nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num), Real.sqrt_pos.mpr (show (5 : ℝ) > (0 : ℝ) by norm_num)]
        · -- x = -Real.sqrt 5, which is valid
          left
          linarith
    · -- x < -4
      rw [abs_of_nonpos (by linarith : x - 1 ≤ 0), abs_of_nonpos (by linarith : x + 4 ≤ 0), abs_of_nonpos (by linarith : x ≤ 0)] at h2
      nlinarith [sq_nonneg (x + 1)]
  · -- Assume x = -√5 ∨ x = 3, prove √(|x - 1| + |x + 4|) = |x|
    rintro (h | h)
    · -- x = -Real.sqrt 5
      have h5 : x = -Real.sqrt 5 := h
      have h1 : Real.sqrt 5 ≥ 0 := Real.sqrt_nonneg 5
      have h6 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
      have h51 : |x - 1| = Real.sqrt 5 + 1 := by
        rw [show x = -Real.sqrt 5 by linarith]
        have h7 : (-Real.sqrt 5 - 1 : ℝ) < 0 := by
          nlinarith [Real.sqrt_nonneg 5, Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num)]
        rw [abs_of_neg h7]
        linarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num)]
      have h52 : |x + 4| = 4 - Real.sqrt 5 := by
        rw [show x = -Real.sqrt 5 by linarith]
        have h8 : (-Real.sqrt 5 + 4 : ℝ) > 0 := by
          nlinarith [Real.sqrt_nonneg 5, Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num)]
        rw [abs_of_pos h8]
        linarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num)]
      have h53 : |x| = Real.sqrt 5 := by
        rw [show x = -Real.sqrt 5 by linarith]
        have h9 : (-Real.sqrt 5: ℝ) < 0 := by
          nlinarith [Real.sqrt_nonneg 5, Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num)]
        rw [abs_of_neg h9]
        linarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num)]
      have h54 : |x - 1| + |x + 4| = (5 : ℝ) := by
        linarith [h51, h52, Real.sqrt_nonneg 5, Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num)]
      rw [h54]
      rw [h53]
      all_goals norm_num [Real.sqrt_nonneg, abs_nonneg, h6]
    · -- x = 3
      rw [h]
      have h54 : |(3 : ℝ) - 1| + |(3 : ℝ) + 4| = (9 : ℝ) := by
        norm_num [abs_of_pos, abs_of_nonneg]
      have h53 : |(3 : ℝ)| = (3 : ℝ) := by
        norm_num [abs_of_nonneg]
      rw [h54]
      rw [h53]
      have : Real.sqrt (9 : ℝ) = (3 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [this]
      all_goals norm_num [Real.sqrt_nonneg, abs_nonneg]