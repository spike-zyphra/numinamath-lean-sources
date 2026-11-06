import Mathlib

theorem algebra_252828 (x : ℝ) : (5^(2*x) : ℝ) - 2 * 5^x - 15 = 0 ↔ x = 1 := by 
  constructor 
  · -- Assume (5^(2*x) : ℝ) - 2 * 5^x - 15 = 0, prove x = 1 
    intro h
    have h1 : (5 : ℝ) ^ (2 * x) = ((5 : ℝ) ^ x) ^ 2 := by 
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul]
      ring_nf 
      all_goals linarith 
    rw [h1] at h
    have h2 : ((5 : ℝ) ^ x - 5 : ℝ) * ((5 : ℝ) ^ x + 3 : ℝ) = 0 := by 
      nlinarith [h, Real.rpow_pos_of_pos (show 0 < (5 : ℝ) by norm_num) x]
    cases' (mul_eq_zero.mp h2) with h3 h4
    · -- Case (5 : ℝ) ^ x - 5 = 0 
      have h5 : (5 : ℝ) ^ x = 5 := by linarith 
      have h6 : x = 1 := by 
        apply_fun (Real.logb (5 : ℝ)) at h5 
        simp at h5 
        linarith 
      linarith 
    · -- Case (5 : ℝ) ^ x + 3 = 0 
      have h7 : (5 : ℝ) ^ x ≤ -3 := by linarith 
      have h8 : (5 : ℝ) ^ x > 0 := by 
        positivity 
      linarith 
  · -- Assume x = 1, prove (5^(2*x) : ℝ) - 2 * 5^x - 15 = 0 
    intro h 
    rw [h] 
    norm_num
    all_goals norm_num 
    all_goals ring_nf 
    <;> norm_num 
    <;> ring 
    <;> norm_num