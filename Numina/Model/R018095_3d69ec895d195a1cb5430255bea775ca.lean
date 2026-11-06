import Mathlib

theorem algebra_281915 (x : ℝ) (h : (10 : ℝ) ^ (2 * x) = 25) : (10 : ℝ) ^ (1 - x) = 2 := by

  have h1 : (10 : ℝ) ^ (2 * x) = ((10 : ℝ) ^ x) ^ 2 := by 
    calc 
      (10 : ℝ) ^ (2 * x) = (10 ^ x) ^ 2 := by 
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        ring_nf 
        all_goals norm_num 
      _ = ((10 : ℝ) ^ x) ^ 2 := by 
        ring_nf

  rw [h1] at h

  have h2 : (10 : ℝ) ^ x = 5 := by
    have h3 : ((10 : ℝ) ^ x) ^ 2 - 25 = 0 := by 
      nlinarith 
    have h4 : ((10 : ℝ) ^ x - 5) * ((10 : ℝ) ^ x + 5) = 0 := by 
      nlinarith 
    cases' (mul_eq_zero.mp h4) with h5 h6
    · -- Case where $10^x - 5 = 0$
      linarith
    · -- Case where $10^x + 5 = 0$
      have h7 : (10 : ℝ) ^ x > 0 := by positivity
      have h8 : (10 : ℝ) ^ x = -5 := by linarith 
      nlinarith

  have h3 : (10 : ℝ) ^ (1 - x) = (10 : ℝ) ^ (1 : ℝ) * ((10 : ℝ) ^ x)⁻¹ := by 
    have h4 : (10 : ℝ) ^ (1 - x) = (10 : ℝ) ^ (1 : ℝ) / (10 : ℝ) ^ x := by
      have h5 : (10 : ℝ) ^ (1 - x) = (10 : ℝ) ^ ((1 : ℝ) - x) := by
        ring_nf
      rw [h5]
      rw [Real.rpow_sub]
      all_goals norm_num 
    rw [h4]
    field_simp
    <;> ring_nf 
  rw [h3]
  rw [h2]
  all_goals norm_num