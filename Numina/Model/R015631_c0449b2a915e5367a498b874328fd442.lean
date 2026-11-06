import Mathlib

open Real

theorem algebra_160478 : sqrt (11 + sqrt 3) / sqrt 59 * sqrt (4 + sqrt (5 + sqrt 3)) * sqrt (3 + sqrt (5 + sqrt (5 + sqrt 3))) * sqrt (3 - sqrt (5 + sqrt (5 + sqrt 3))) = sqrt 2 := by
  have h1 : sqrt (11 + sqrt 3) / sqrt 59 * sqrt (4 + sqrt (5 + sqrt 3)) * sqrt (3 + sqrt (5 + sqrt (5 + sqrt 3))) * sqrt (3 - sqrt (5 + sqrt (5 + sqrt 3))) = 
    (sqrt (11 + sqrt 3) * sqrt (4 + sqrt (5 + sqrt 3)) * (sqrt (3 + sqrt (5 + sqrt (5 + sqrt 3))) * sqrt (3 - sqrt (5 + sqrt (5 + sqrt 3)))) ) / sqrt 59 := by ring
  have h6 : sqrt (3 + sqrt (5 + sqrt (5 + sqrt 3))) * sqrt (3 - sqrt (5 + sqrt (5 + sqrt 3))) = sqrt (4 - sqrt (5 + sqrt 3)) := by
    have h2 : sqrt (3 + sqrt (5 + sqrt (5 + sqrt 3))) * sqrt (3 - sqrt (5 + sqrt (5 + sqrt 3))) = sqrt ((3 + sqrt (5 + sqrt (5 + sqrt 3))) * (3 - sqrt (5 + sqrt (5 + sqrt 3)))) := by 
      rw [← sqrt_mul (by positivity)]
    have h3 : (3 + sqrt (5 + sqrt (5 + sqrt 3))) * (3 - sqrt (5 + sqrt (5 + sqrt 3))) = 9 - (sqrt (5 + sqrt (5 + sqrt 3)) )^2 := by nlinarith
    have h4 : (sqrt (5 + sqrt (5 + sqrt 3)) )^2 = 5 + sqrt (5 + sqrt 3) := by 
      rw [Real.sq_sqrt]
      positivity
    have h5 : (3 + sqrt (5 + sqrt (5 + sqrt 3))) * (3 - sqrt (5 + sqrt (5 + sqrt 3))) = 4 - sqrt (5 + sqrt 3) := by
      nlinarith [h3, h4]
    rw [h2]
    rw [h5]
  have h7 : sqrt (4 + sqrt (5 + sqrt 3)) * (sqrt (3 + sqrt (5 + sqrt (5 + sqrt 3))) * sqrt (3 - sqrt (5 + sqrt (5 + sqrt 3)))) = sqrt (11 - sqrt 3) := by
    have h8 : sqrt (4 + sqrt (5 + sqrt 3)) * (sqrt (3 + sqrt (5 + sqrt (5 + sqrt 3))) * sqrt (3 - sqrt (5 + sqrt (5 + sqrt 3)))) = 
      sqrt (4 + sqrt (5 + sqrt 3)) * sqrt (4 - sqrt (5 + sqrt 3)) := by 
      rw [show sqrt (3 + sqrt (5 + sqrt (5 + sqrt 3))) * sqrt (3 - sqrt (5 + sqrt (5 + sqrt 3))) = sqrt (4 - sqrt (5 + sqrt 3)) by linarith [h6]]
    rw [h8]
    have h9 : sqrt (4 + sqrt (5 + sqrt 3)) * sqrt (4 - sqrt (5 + sqrt 3)) = sqrt ((4 + sqrt (5 + sqrt 3)) * (4 - sqrt (5 + sqrt 3))) := by 
      rw [← sqrt_mul (by positivity)]
    rw [h9]
    have h10 : (4 + sqrt (5 + sqrt 3)) * (4 - sqrt (5 + sqrt 3)) = 11 - sqrt 3  := by
      nlinarith [Real.sqrt_nonneg (5 + sqrt 3), Real.sq_sqrt (show (5 + sqrt 3) ≥ 0 by positivity), Real.sq_sqrt (show (3) ≥ 0 by positivity)]
    rw [h10]
  have h8 : sqrt (11 + sqrt 3) * (sqrt (4 + sqrt (5 + sqrt 3)) * (sqrt (3 + sqrt (5 + sqrt (5 + sqrt 3))) * sqrt (3 - sqrt (5 + sqrt (5 + sqrt 3))))) = sqrt 118 := by
    have h9 : sqrt (11 + sqrt 3) * (sqrt (4 + sqrt (5 + sqrt 3)) * (sqrt (3 + sqrt (5 + sqrt (5 + sqrt 3))) * sqrt (3 - sqrt (5 + sqrt (5 + sqrt 3))))) = sqrt (11 + sqrt 3) * (sqrt (11 - sqrt 3)) := by
      rw [show sqrt (4 + sqrt (5 + sqrt 3)) * (sqrt (3 + sqrt (5 + sqrt (5 + sqrt 3))) * sqrt (3 - sqrt (5 + sqrt (5 + sqrt 3)))) = sqrt (11 - sqrt 3) by linarith [h7]]
    rw [h9]
    have h11 : sqrt (11 + sqrt 3) * sqrt (11 - sqrt 3) = sqrt ((11 + sqrt 3) * (11 - sqrt 3)) := by 
      rw [← sqrt_mul (by positivity)]
    rw [h11]
    have h12 : (11 + sqrt 3) * (11 - sqrt 3) = 118 := by
      nlinarith [Real.sqrt_nonneg (3) , Real.sq_sqrt (show (3) ≥ 0 by positivity)]
    rw [h12]
  rw [h1]
  rw [show (sqrt (11 + sqrt 3) * sqrt (4 + sqrt (5 + sqrt 3)) * (sqrt (3 + sqrt (5 + sqrt (5 + sqrt 3))) * sqrt (3 - sqrt (5 + sqrt (5 + sqrt 3)))) ) / sqrt 59 = 
      sqrt (118) / sqrt 59 by 
        rw [show sqrt (11 + sqrt 3) * sqrt (4 + sqrt (5 + sqrt 3)) * (sqrt (3 + sqrt (5 + sqrt (5 + sqrt 3))) * sqrt (3 - sqrt (5 + sqrt (5 + sqrt 3)))) = sqrt (118) by linarith [h8]]
  ]
  -- Now show sqrt(118)/sqrt(59) = sqrt(2)
  have h13 : sqrt (118) / sqrt 59 = sqrt 2 := by
    have h14 : sqrt (118) = sqrt (2 * 59) := by
      norm_num
    rw [h14]
    have h15 : sqrt (2 * 59) / sqrt 59 = sqrt 2 := by
      field_simp [Real.sqrt_mul]
    rw [h15]
  rw [h13]