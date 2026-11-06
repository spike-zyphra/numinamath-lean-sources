import Mathlib

theorem algebra_10196 (x : ℝ) :
    Real.sqrt (3 * x + 5) / Real.sqrt (6 * x + 5) = Real.sqrt 5 / 3 ↔ x = 20 / 3 := by
  constructor
  · -- Assume $\frac{\sqrt{3x+5}}{\sqrt{6x+5}}=\frac{\sqrt{5}}{3}$, prove $x = \frac{20}{3}$
    intro h
    have h1 : 0 < 6 * x + 5 := by
      by_contra h1
      push_neg at h1
      have h1' : Real.sqrt (6 * x + 5) = 0 := by
        rw [Real.sqrt_eq_zero'.mpr]
        linarith
      have h2 : Real.sqrt (3 * x + 5) / Real.sqrt (6 * x + 5) = 0 := by
        rw [h1']
        norm_num
      have h3 : Real.sqrt 5 / 3 = 0 := by
        linarith [h, h2]
      have h4 : Real.sqrt 5 > 0 := by
        apply Real.sqrt_pos.mpr
        norm_num
      have h5 : Real.sqrt 5 / 3 > 0 := by
        positivity
      linarith [h3, h5]
    have h2 : 0 ≤ 3 * x + 5 := by
      by_contra h2
      push_neg at h2
      have h2' : Real.sqrt (3 * x + 5) = 0 := by
        rw [Real.sqrt_eq_zero'.mpr]
        linarith
      have h3 : Real.sqrt (3 * x + 5) / Real.sqrt (6 * x + 5) = 0 := by
        rw [h2']
        norm_num
      have h4 : Real.sqrt 5 / 3 = 0 := by
        linarith [h, h3]
      have h4 : Real.sqrt 5 > 0 := by
        apply Real.sqrt_pos.mpr
        norm_num
      have h5 : Real.sqrt 5 / 3 > 0 := by
        positivity
      linarith [h4, h5]
    have h3 : 3 * Real.sqrt (3 * x + 5) = Real.sqrt 5 * Real.sqrt (6 * x + 5) := by
      have h4 : Real.sqrt (6 * x + 5) > 0 := by
        apply Real.sqrt_pos.mpr
        linarith
      have eq1 : Real.sqrt (3 * x + 5) / Real.sqrt (6 * x + 5) = Real.sqrt 5 / 3 := by
        linarith [h]
      field_simp at eq1
      <;> nlinarith [Real.sqrt_nonneg (3 * x + 5), Real.sqrt_nonneg (6 * x + 5)]
    have h4 : (3 * Real.sqrt (3 * x + 5)) ^ 2 = (Real.sqrt 5 * Real.sqrt (6 * x + 5)) ^ 2 := by
      rw [h3]
    have h5 : (3 * Real.sqrt (3 * x + 5)) ^ 2 = 9 * (3 * x + 5) := by
      calc
        (3 * Real.sqrt (3 * x + 5)) ^ 2 = 9 * (Real.sqrt (3 * x + 5) ^ 2) := by
          ring
        _ = 9 * (3 * x + 5) := by
          rw [Real.sq_sqrt]
          linarith
    have h6 : (Real.sqrt 5 * Real.sqrt (6 * x + 5)) ^ 2 = 5 * (6 * x + 5) := by
      calc
        (Real.sqrt 5 * Real.sqrt (6 * x + 5)) ^ 2 = Real.sqrt 5 ^ 2 * (Real.sqrt (6 * x + 5) ^ 2) := by
          ring
        _ = 5 * (6 * x + 5) := by
          rw [Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (6 * x + 5 : ℝ) by nlinarith)]
          all_goals nlinarith
    have eq1 : 9 * (3 * x + 5) = 5 * (6 * x + 5) := by
      nlinarith [Real.sqrt_nonneg (3 * x + 5), Real.sqrt_nonneg (6 * x + 5), Real.sqrt_nonneg (5 : ℝ), h4, h5, h6]
    nlinarith
  · -- Assume x = 20/3, prove the equation
    intro h
    rw [show x = (20 / 3 : ℝ) by linarith]
    have h1 : Real.sqrt (3 * (20 / 3 : ℝ) + 5) = (5 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h2 : Real.sqrt (6 * (20 / 3 : ℝ) + 5) = Real.sqrt (45 : ℝ) := by
      norm_num
    have h3 : Real.sqrt (45 : ℝ) = 3 * Real.sqrt (5 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    rw [h1, h2, h3]
    field_simp
    <;> nlinarith [Real.sqrt_pos.mpr (show 0 < (5 : ℝ) by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num : (0 : ℝ) ≤ (5 : ℝ)), Real.sqrt_nonneg (5 : ℝ)]