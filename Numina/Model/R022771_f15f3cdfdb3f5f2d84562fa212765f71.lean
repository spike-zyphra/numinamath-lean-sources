import Mathlib

theorem number_theory_277340 :
    ¬∃ a d : ℚ, √2 = a + d ∧ √3 = a + 2 * d ∧ √5 = a + 3 * d := by 
  rintro ⟨a, d, h₁, h₂, h₃⟩
  have h4 : (d : ℝ) = √3 - √2 := by
    ring_nf at h₁ h₂ 
    linarith 
  have h5 : (d : ℝ) = √5 - √3 := by 
    ring_nf at h₂ h₃ 
    linarith 
  have h6 : √3 - √2 = √5 - √3 := by 
    linarith [h4, h5]
  have h7 : 2 * √3 = √2 + √5 := by
    linarith [h6]
  have h8 : (2 * √3) ^ 2 = (√2 + √5) ^ 2 := by 
    rw [h7]
  have h9 : (2 * √3) ^ 2 = 12 := by
    calc
      (2 * √3) ^ 2 = 4 * (√3 ^ 2) := by ring
      _ = 4 * 3 := by rw [Real.sq_sqrt]; positivity
      _ = 12 := by norm_num
  have h10 : (√2 + √5) ^ 2 = 7 + 2 * √10 := by
    have h11 : (√2 + √5) ^ 2 = (√2)^2 + (√5)^2 + 2 * (√2 * √5) := by ring
    rw [h11]
    have h12 : (√2)^2 = 2 := Real.sq_sqrt (by norm_num)
    have h13 : (√5)^2 = 5 := Real.sq_sqrt (by norm_num)
    have h14 : √2 * √5 = √10 := by
      rw [← Real.sqrt_mul (by norm_num)]
      norm_num
    rw [h12, h13, h14]
    all_goals norm_num
    all_goals ring_nf <;> norm_num [Real.sqrt_nonneg]
  rw [h9, h10] at h8
  have h11 : 5 = 2 * √10 := by
    nlinarith
  have h12 : (5 : ℝ) ^ 2 = (2 * √10) ^ 2 := by
    rw [h11]
  have h13 : (5 : ℝ) ^ 2 = 25 := by norm_num
  have h14 : (2 * √10) ^ 2 = 40 := by
    calc
      (2 * √10) ^ 2 = 4 * (√10 ^ 2) := by ring
      _ = 4 * 10 := by rw [Real.sq_sqrt]; positivity
      _ = 40 := by norm_num
  rw [h13, h14] at h12
  all_goals nlinarith