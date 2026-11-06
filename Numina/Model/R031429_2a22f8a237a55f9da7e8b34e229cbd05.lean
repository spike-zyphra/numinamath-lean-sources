import Mathlib

theorem algebra_20467 : Complex.abs (1 - Complex.I)^8 = 16 := by 
  have h1 : (1 - Complex.I) ^ 8 = 16 := by 
    have h2 : (1 - Complex.I) ^ 2 = -2 * Complex.I := by 
      simp [pow_two, Complex.ext_iff, Complex.I_mul_I]
      <;> norm_num 
      <;> ring 
    have h4 : (1 - Complex.I) ^ 4 = -4 := by
      calc 
        (1 - Complex.I) ^ 4 = ((1 - Complex.I) ^ 2) ^ 2 := by ring 
        _ = (-2 * Complex.I) ^ 2 := by rw [h2]
        _ = (-2) ^ 2 * (Complex.I) ^ 2 := by ring 
        _ = 4 * (-1) := by norm_num [Complex.I_sq]
        _ = -4 := by ring 
    calc 
      (1 - Complex.I) ^ 8 = ((1 - Complex.I) ^ 4) ^ 2 := by ring 
      _ = (-4) ^ 2 := by rw [h4]
      _ = 16 := by norm_num 
  have h6 : Complex.abs (1 - Complex.I) = Real.sqrt 2 := by
    simp [Complex.abs, Complex.normSq, Complex.I_mul_I]
    <;> norm_num
  calc 
    Complex.abs (1 - Complex.I) ^ 8 = (Complex.abs (1 - Complex.I)) ^ 8 := by ring 
    _ = (Real.sqrt 2) ^ 8 := by rw [h6]
    _ = ((Real.sqrt 2) ^ 2) ^ 4 := by ring
    _ = (2) ^ 4 := by rw [Real.sq_sqrt]; all_goals norm_num 
    _ = 16 := by norm_num