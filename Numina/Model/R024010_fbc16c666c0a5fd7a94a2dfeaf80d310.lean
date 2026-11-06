import Mathlib

theorem algebra_858 (x : ℝ) (hx : x > 0) : (16 * x^16) ^ ((1 : ℝ) / 2) = 4 * x^8 := by
  have h1 : (16 * x ^ 16 : ℝ) ^ ((1 : ℝ) / 2) = (16 : ℝ) ^ ((1 : ℝ) / 2) * ((x ^ 16 : ℝ) ) ^ ((1 : ℝ) / 2) := by
    rw [← Real.mul_rpow]
    all_goals
      positivity

  have h2 : (16 : ℝ) ^ ((1 : ℝ) / 2) = (4 : ℝ) := by
    have h3 : (16 : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt (16 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]
    rw [h3]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num

  have h4 : ((x ^ 16 : ℝ) ) ^ ((1 : ℝ) / 2) = (x ^ 8 : ℝ) := by
    have h5 : ((x ^ 16 : ℝ) ) ^ ((1 : ℝ) / 2) = ( (x ^ 16) ^ ((1 / 2 : ℝ) ) ) := by
      rfl
    rw [h5]
    have h7 : ( (x ^ 16) ^ ((1 / 2 : ℝ) ) ) = (x ^ (8 : ℝ) ) := by
      have h9 : (x ^ 16 : ℝ) = (x) ^ (16 : ℝ) := by
        norm_cast
      rw [h9]
      have h10 : ( (x) ^ (16 : ℝ) ) ^ ( (1 / 2 : ℝ) ) = (x) ^ ( (16 * (1 / 2) : ℝ ) ) := by
        rw [← Real.rpow_mul]
        ring_nf
        all_goals
          positivity
      have h11 : (x) ^ ( (16 * (1 / 2) : ℝ ) ) = x ^ (8 : ℝ) := by
        norm_num
      rw [h10, h11]
    rw [h7]
    all_goals
      norm_cast

  rw [h1]
  rw [h2, h4]
  all_goals
    norm_cast
    all_goals
      ring