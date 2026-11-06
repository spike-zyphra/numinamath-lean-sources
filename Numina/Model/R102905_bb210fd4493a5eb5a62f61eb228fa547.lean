import Mathlib

theorem algebra_185069 {x : ℝ} (hx : x = (Real.sqrt 7 - 5) / 2) :
    (x + 1) * (x + 2) * (x + 3) * (x + 4) = -3 / 4 := by
  have h1 : x + 1 = (Real.sqrt 7 - 3) / 2 := by 
    rw [hx]
    ring 
  have h2 : x + 2 = (Real.sqrt 7 - 1) / 2 := by 
    rw [hx]
    ring 
  have h3 : x + 3 = (Real.sqrt 7 + 1) / 2 := by 
    rw [hx]
    ring 
  have h4 : x + 4 = (Real.sqrt 7 + 3) / 2 := by 
    rw [hx]
    ring 
  rw [h1, h2, h3, h4]
  have h5 : ((Real.sqrt 7 - 3) / 2) * ((Real.sqrt 7 - 1) / 2) * ((Real.sqrt 7 + 1) / 2) * ((Real.sqrt 7 + 3) / 2) = 
         ((Real.sqrt 7 - 3) * (Real.sqrt 7 + 3) * (Real.sqrt 7 - 1) * (Real.sqrt 7 + 1)) / 16 := by 
    ring 
  rw [h5]
  have h6 : (Real.sqrt 7 - 3) * (Real.sqrt 7 + 3) = -2 := by 
    calc
      (Real.sqrt 7 - 3) * (Real.sqrt 7 + 3) = (Real.sqrt 7)^2 - 9 := by ring 
      _ = 7 - 9 := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num : (7 : ℝ) ≥ 0)]
      _ = -2 := by norm_num 
  have h7 : (Real.sqrt 7 - 1) * (Real.sqrt 7 + 1) = 6 := by 
    calc 
      (Real.sqrt 7 - 1) * (Real.sqrt 7 + 1) = (Real.sqrt 7)^2 - 1 := by ring 
      _ = 7 - 1 := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num : (7 : ℝ) ≥ 0)]
      _ = 6 := by norm_num 
  have h8 : (Real.sqrt 7 - 3) * (Real.sqrt 7 + 3) * (Real.sqrt 7 - 1) * (Real.sqrt 7 + 1) = -12 := by 
    calc 
      (Real.sqrt 7 - 3) * (Real.sqrt 7 + 3) * (Real.sqrt 7 - 1) * (Real.sqrt 7 + 1) = ((Real.sqrt 7 - 3) * (Real.sqrt 7 + 3)) * ((Real.sqrt 7 - 1) * (Real.sqrt 7 + 1)) := by ring 
      _ = (-2) * (6) := by rw [h6, h7] 
      _ = -12 := by norm_num 
  rw [h8]
  norm_num