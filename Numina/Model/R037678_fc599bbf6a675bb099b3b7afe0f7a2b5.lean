import Mathlib

theorem algebra_12848
    (A R M L : ℝ)
    (h₀ : 0 < A)
    (h₁ : 0 < R)
    (h₂ : 0 < M)
    (h₃ : 0 < L)
    (h₄ : Real.logb 10 (A * L) + Real.logb 10 (A * M) = 2)
    (h₅ : Real.logb 10 (M * L) + Real.logb 10 (M * R) = 3)
    (h₆ : Real.logb 10 (R * A) + Real.logb 10 (R * L) = 4) :
    A * R * M * L = 1000 := by

  have h7 : Real.logb 10 (A * L) = Real.logb 10 A + Real.logb 10 L := by
    rw [Real.logb_mul (by positivity) (by positivity)]
    
  have h8 : Real.logb 10 (A * M) = Real.logb 10 A + Real.logb 10 M := by
    rw [Real.logb_mul (by positivity) (by positivity)]
    
  have h9 : Real.logb 10 (M * L) = Real.logb 10 M + Real.logb 10 L := by
    rw [Real.logb_mul (by positivity) (by positivity)]
    
  have h10 : Real.logb 10 (M * R) = Real.logb 10 M + Real.logb 10 R := by
    rw [Real.logb_mul (by positivity) (by positivity)]
    
  have h11 : Real.logb 10 (R * A) = Real.logb 10 R + Real.logb 10 A := by
    rw [Real.logb_mul (by positivity) (by positivity)]
    
  have h12 : Real.logb 10 (R * L) = Real.logb 10 R + Real.logb 10 L := by
    rw [Real.logb_mul (by positivity) (by positivity)]
    
  rw [h7, h8] at h₄
  rw [h9, h10] at h₅
  rw [h11, h12] at h₆
  
  have h13 : Real.logb 10 A + Real.logb 10 L + Real.logb 10 M + Real.logb 10 R = 3 := by
    nlinarith
  
  have h14 : Real.logb 10 (A * R * M * L) = 3 := by
    have h15 : Real.logb 10 (A * R * M * L) = Real.logb 10 A + Real.logb 10 R + Real.logb 10 M + Real.logb 10 L := by
      simp [Real.logb_mul, h₀.ne.symm, h₁.ne.symm, h₂.ne.symm, h₃.ne.symm]
      <;> linarith
    linarith [h13, h15]

  have h16 : A * R * M * L = (10 : ℝ) ^ (3 : ℝ) := by
    rw [←h14]
    field_simp [Real.rpow_logb, h₀, h₁, h₂, h₃]
    all_goals linarith
  
  rw [h16]
  norm_num