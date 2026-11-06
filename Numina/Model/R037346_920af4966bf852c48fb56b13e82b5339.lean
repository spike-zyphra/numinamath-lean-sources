import Mathlib

theorem algebra_6772 {r : ℝ} (hr : 2 * r - 1 > 0) :
    Real.logb 81 (2 * r - 1) = -1 / 2 ↔ r = 5 / 9 := by
  constructor
  · -- Assume $\log_{81} (2 * r - 1) = -1 / 2$, prove $r = 5 / 9$
    intro h_eq
    have h1 : (2 * r - 1) = (81 : ℝ) ^ (-1 / 2 : ℝ) := by
      rw [← h_eq]
      field_simp [Real.rpow_logb, show (81 : ℝ) > 1 by norm_num, show (2 * r - 1) > 0 by linarith]
    have h2 : (81 : ℝ) ^ (-1 / 2 : ℝ) = 1 / 9 := by
      have h3 : (81 : ℝ) ^ (-1 / 2 : ℝ) = ( (3 : ℝ) ^ (4 : ℝ) ) ^ (-1 / 2 : ℝ) := by norm_num
      rw [h3]
      have h4 : ( ( (3 : ℝ) ^ (4 : ℝ) ) ) ^ (-1 / 2 : ℝ) = (3 : ℝ) ^ (-2 : ℝ) := by
        rw [← Real.rpow_mul]
        ring_nf
        all_goals norm_num
      rw [h4]
      norm_num
    rw [h2] at h1
    have h3 : 2 * r = 10 / 9 := by
      nlinarith
    linarith
  · -- Assume $r = 5 / 9$, prove $\log_{81} (2 * r - 1) = -1 / 2$
    intro h_eq
    rw [h_eq]
    have h3 : Real.logb 81 (2 * (5 / 9 : ℝ) - 1) = -1 / 2 := by
      rw [show (2 * (5 / 9 : ℝ) - 1) = (1 / 9 : ℝ) by norm_num]
      rw [Real.logb]
      have h1 : Real.log (81 : ℝ) = 4 * Real.log (3 : ℝ) := by
        rw [show (81 : ℝ) = (3 : ℝ) ^ (4 : ℝ) by norm_num]
        simp [Real.log_rpow]
      have h2 : Real.log (1 / 9 : ℝ) = -2 * Real.log (3 : ℝ) := by
        calc
          Real.log (1 / 9 : ℝ) = Real.log ( (3 : ℝ) ^ (-2 : ℝ) ) := by norm_num
          _ = -2 * Real.log (3 : ℝ) := by
            simp [Real.log_rpow]
      rw [h1, h2]
      field_simp
      <;> ring
    linarith [h3]