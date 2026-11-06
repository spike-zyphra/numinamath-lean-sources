import Mathlib

theorem algebra_305513 {x : ℝ} (hx : x = (Real.sqrt 21 - 5) / 2) :
    x * (x + 1) * (x + 2) * (x + 3) * (x + 4) * (x + 5) = -15 := by
  have h1 : x = (Real.sqrt 21 - 5) / 2 := hx

  have h2 : 2 * x + 5 = Real.sqrt 21 := by
    rw [h1]
    ring

  have h3 : (2 * x + 5) ^ 2 = 21 := by
    rw [h2]
    exact Real.sq_sqrt (by norm_num)
  
  have h4 : 4 * x^2 + 20 * x + 4 = 0 := by
    nlinarith

  have h5 : x^2 + 5 * x + 1 = 0 := by 
    nlinarith

  have h6 : x^2 + 5 * x = -1 := by
    linarith

  have h7 : x * (x + 5) = -1 := by
    nlinarith [h6]

  have h8 : (x + 1) * (x + 4) = 3 := by
    nlinarith [h6]

  have h9 : (x + 2) * (x + 3) = 5 := by
    nlinarith [h6]

  calc
    x * (x + 1) * (x + 2) * (x + 3) * (x + 4) * (x + 5)
      = (x * (x + 5)) * ((x + 1) * (x + 4)) * ((x + 2) * (x + 3)) := by ring
    _ = (-1) * (3) * (5) := by rw [h7, h8, h9]
    _ = -15 := by norm_num