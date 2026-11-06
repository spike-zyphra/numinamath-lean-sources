import Mathlib

theorem algebra_120613 {x : ℝ} (hx : 8^x * (3 * x + 1) = 4) :
    x = 1 / 3 := by
  have h1 : (8 : ℝ) ^ x = 2 ^ (3 * x) := by
    calc
      (8 : ℝ) ^ x = (2 ^ (3 : ℝ) ) ^ x := by norm_num
      _ = 2 ^ (3 * x) := by
        rw [← Real.rpow_mul]
        ring
        all_goals norm_num
  rw [h1] at hx
  by_cases h : 3 * x + 1 > 0
  · -- 3x + 1 > 0
    have h3 : (2 : ℝ) ^ (3 * x) * (3 * x + 1) = (4 : ℝ) := by linarith
    have h4 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (3 * x) * (3 * x + 1)) = Real.logb (2 : ℝ) (4 : ℝ) := by
      rw [h3]
    have h5 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (3 * x) * (3 * x + 1)) = Real.logb (2 : ℝ) ((2 : ℝ) ^ (3 * x)) + Real.logb (2 : ℝ) (3 * x + 1) := by
      rw [Real.logb_mul (by positivity) (by linarith)]
    have h6 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (3 * x)) = (3 * x : ℝ) := by
      rw [Real.logb_rpow]
      all_goals norm_num
    have h7 : Real.logb (2 : ℝ) (4 : ℝ) = (2 : ℝ) := by
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
    rw [h5, h6] at h4
    rw [h7] at h4
    have h8 : 3 * x + 1 > 0 := by linarith
    have h9 : (3 * x + 1) + Real.logb (2 : ℝ) (3 * x + 1) = (3 : ℝ) := by
      nlinarith [h4]
    have h10 : (3 * x + 1) = (2 : ℝ) := by
      by_cases h11 : (3 * x + 1) < (2 : ℝ)
      · -- Assume (3 * x + 1) < 2
        have h12 : Real.logb (2 : ℝ) (3 * x + 1) < (1 : ℝ) := by
          have h13 : Real.logb (2 : ℝ) (3 * x + 1) < Real.logb (2 : ℝ) (2 : ℝ) := by
            apply Real.logb_lt_logb
            all_goals nlinarith
          have h14 : Real.logb (2 : ℝ) (2 : ℝ) = (1 : ℝ) := by
            rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
          nlinarith [h13, h14]
        nlinarith [h12, h9]
      by_cases h12 : (3 * x + 1) > (2 : ℝ)
      · -- Assume (3 * x + 1) > 2
        have h13 : Real.logb (2 : ℝ) (3 * x + 1) > (1 : ℝ) := by
          have h14 : Real.logb (2 : ℝ) (3 * x + 1) > Real.logb (2 : ℝ) (2 : ℝ) := by
            apply Real.logb_lt_logb
            all_goals nlinarith
          have h15 : Real.logb (2 : ℝ) (2 : ℝ) = (1 : ℝ) := by
            rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
          nlinarith [h14, h15]
        nlinarith [h13, h9]
      linarith
    linarith [h10]
  · -- 3 * x + 1 ≤ 0
    have h5 : 3 * x + 1 ≤ (0 : ℝ) := by linarith
    have h6 : (2 : ℝ) ^ (3 * x) > 0 := by positivity
    nlinarith [h6, h5]