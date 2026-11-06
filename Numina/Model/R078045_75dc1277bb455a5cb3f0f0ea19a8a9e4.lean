import Mathlib

theorem algebra_303524 {x : ℝ} (hx : x = (Real.sqrt 29 - 3) / 2) :
    x ^ 4 + 5 * x ^ 3 - 3 * x ^ 2 - 8 * x + 9 = 7 * Real.sqrt 29 - 32 := by
  have h1 : x = (Real.sqrt 29 - 3) / 2 := hx
  
  have h2 : 2 * x + 3 = Real.sqrt 29 := by
    rw [h1]
    ring
  
  have h3 : (2 * x + 3) ^ 2 = (Real.sqrt 29) ^ 2 := by 
    rw [h2]
  
  have h4 : (2 * x + 3) ^ 2 = 4 * x ^ 2 + 12 * x + 9 := by ring
  
  have h5 : (Real.sqrt 29) ^ 2 = (29 : ℝ) := Real.sq_sqrt (by norm_num)
  
  have h6 : 4 * x ^ 2 + 12 * x + 9 = (29 : ℝ) := by
    rw [h4, h5] at h3
    linarith
  
  have h7 : x ^ 2 + 3 * x - 5 = (0 : ℝ) := by
    nlinarith
  
  have h_eq1 : x ^ 2 = -3 * x + 5 := by
    linarith [h7]

  have h_eq2 : x^3 = 14 * x - 15 := by 
    calc
      x^3 = x * x^2 := by ring
      _ = x * (-3 * x + 5) := by rw [h_eq1]
      _ = -3 * x^2 + 5 * x := by ring
      _ = -3 * (-3 * x + 5) + 5 * x := by rw [h_eq1]
      _ = 9 * x - 15 + 5 * x := by ring
      _ = 14 * x - 15 := by ring

  have h_eq3 : x^4 = -57 * x + 70 := by 
    calc
      x^4 = (x^2) ^ 2 := by ring
      _ = (-3 * x + 5) ^ 2 := by rw [h_eq1]
      _ = 9 * x^2 - 30 * x + 25 := by ring
      _ = 9 * (-3 * x + 5) - 30 * x + 25 := by rw [h_eq1]
      _ = -27 * x + 45 - 30 * x + 25 := by ring
      _ = -57 * x + 70 := by ring
  
  have eq : x ^ 4 + 5 * x ^ 3 - 3 * x ^ 2 - 8 * x + 9 = 14 * x - 11 := by
    rw [h_eq3, h_eq2, h_eq1]
    linarith
  
  rw [eq]
  rw [h1]
  ring