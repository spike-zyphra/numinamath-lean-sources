import Mathlib

theorem algebra_202427 (x : ℝ) : 5 * (0.16 : ℝ) ^ x + 8 * (0.4 : ℝ) ^ x = 4 ↔ x = 1 := by
  constructor
  · -- Assume 5 * 0.16^x + 8 * 0.4^x = 4, prove x = 1
    intro h_eq
    have h1 : (0.16 : ℝ) ^ x = (0.4 : ℝ) ^ x * (0.4 : ℝ) ^ x := by
      have h2 : (0.16 : ℝ) = (0.4 : ℝ) ^ (2 : ℝ) := by norm_num
      rw [h2]
      have h3 : ((0.4 : ℝ) ^ (2 : ℝ)) ^ x = (0.4 : ℝ) ^ (2 * x : ℝ) := by
        rw [← Real.rpow_mul]
        ring
        all_goals norm_num
      have h4 : (0.4 : ℝ) ^ (2 * x : ℝ) = ((0.4 : ℝ) ^ x) ^ 2 := by
        have h5 : (0.4 : ℝ) ^ (2 * x : ℝ) = ((0.4 : ℝ) ^ x) ^ 2 := by
          calc
            (0.4 : ℝ) ^ (2 * x : ℝ) = (0.4 : ℝ) ^ (x * (2 : ℝ)) := by ring_nf
            _ = ((0.4 : ℝ) ^ x) ^ (2 : ℝ) := by rw [← Real.rpow_mul]; ring_nf; all_goals norm_num
            _ = ((0.4 : ℝ) ^ x) ^ 2 := by norm_cast
        linarith
      rw [h3, h4]
      <;> ring
    have h2 : 5 * ((0.4 : ℝ) ^ x * (0.4 : ℝ) ^ x) + 8 * (0.4 : ℝ) ^ x = 4 := by
      rw [h1] at h_eq
      linarith
    have h3 : ((0.4 : ℝ) ^ x) ^ 2 = (0.4 : ℝ) ^ x * (0.4 : ℝ) ^ x := by
      ring_nf
    have h4 : 5 * ((0.4 : ℝ) ^ x) ^ 2 + 8 * ((0.4 : ℝ) ^ x) - 4 = 0 := by
      nlinarith [h2, h3]
    have h5 : ((0.4 : ℝ) ^ x - 2 / 5) * ((0.4 : ℝ) ^ x + 2) = 0 := by
      nlinarith [h4]
    cases' (mul_eq_zero.mp h5) with h6 h7
    · -- Case $ (0.4 : ℝ) ^ x - 2 / 5 = 0 $
      have h8 : (0.4 : ℝ) ^ x = (2 / 5 : ℝ) := by linarith
      have h9 : x = 1 := by
        have h10 : Real.logb (0.4 : ℝ) ((0.4 : ℝ) ^ x) = Real.logb (0.4 : ℝ) (2 / 5 : ℝ) := by
          rw [h8]
        have h11 : Real.logb (0.4 : ℝ) ((0.4 : ℝ) ^ x) = x := by
          have h12 : Real.logb (0.4 : ℝ) ((0.4 : ℝ) ^ x) = x := by
            rw [Real.logb_rpow]
            all_goals norm_num
          linarith
        have h13 : Real.logb (0.4 : ℝ) (2 / 5 : ℝ) = (1 : ℝ) := by
          have h14 : Real.logb (0.4 : ℝ) (2 / 5 : ℝ) = (1 : ℝ) := by
            rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
          linarith
        rw [h11] at h10
        rw [h13] at h10
        linarith
      exact h9
    · -- Case $0.4^x + 2 = 0$
      have h8 : (0.4 : ℝ) ^ x = (-2 : ℝ) := by linarith
      have h9 : (0.4 : ℝ) ^ x > 0 := by positivity
      nlinarith
  · -- Assume x = 1, prove the equation
    intro h_eq
    rw [h_eq]
    norm_num