import Mathlib

theorem algebra_4095 :
    IsLeast {d | ∃ y, d = Real.sqrt ((6 - y ^ 2 / 2) ^ 2 + (12 - y) ^ 2)} (2 * Real.sqrt 17) := by 
  constructor
  · -- First, show that $2\sqrt{17}$ is indeed achievable, so there exists a y such that the distance is $2\sqrt{17}$ 
    use 4
    have h1 : (6 - (4:ℝ) ^ 2 / 2) ^ 2 + (12 - (4:ℝ)) ^ 2 = 68 := by norm_num
    have h2 : Real.sqrt ((6 - (4:ℝ) ^ 2 / 2) ^ 2 + (12 - (4:ℝ)) ^ 2) = Real.sqrt 68 := by
      rw [h1]
    have h3 : Real.sqrt 68 = 2 * Real.sqrt 17 := by
      calc
        Real.sqrt 68 = Real.sqrt (2^2 * 17) := by norm_num
        _ = (2 : ℝ) * Real.sqrt 17 := by rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
    rw [h2, h3]
  
  · -- Now show that $2\sqrt{17}$ is a lower bound
    intro d hd
    rcases hd with ⟨y, hy⟩
    have h4 : (6 - y ^ 2 / 2) ^ 2 + (12 - y) ^ 2 ≥ 68 := by 
      nlinarith [sq_nonneg (y - 4), sq_nonneg (y + 4)]
    
    have h5 : Real.sqrt ((6 - y ^ 2 / 2) ^ 2 + (12 - y) ^ 2) ≥ Real.sqrt 68 := Real.sqrt_le_sqrt (h4)
    
    have h6 : Real.sqrt 68 = 2 * Real.sqrt 17 := by 
      calc 
        Real.sqrt 68 = Real.sqrt (2^2 * 17) := by norm_num
        _ = (2 : ℝ) * Real.sqrt 17 := by rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
    
    linarith [hy, h5, h6]