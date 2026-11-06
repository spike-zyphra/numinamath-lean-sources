import Mathlib

theorem algebra_214783 {x y : ℝ} (h1 : x^3 - 2023 * x = y^3 - 2023 * y + 2020) (h2 : x^2 + x * y + y^2 = 2022) :
    x - y = -2020 := by 
  have eq2 : (x^3 - 2023 * x) - (y^3 - 2023 * y) = 2020 := by linarith 
  have eq3' : (x - y) * (x^2 + x * y + y^2 - 2023) = 2020 := by 
    have eq4 : x^3 - y^3 = (x - y) * (x^2 + x * y + y^2) := by 
      ring 
    have eq5 : (x^3 - 2023 * x) - (y^3 - 2023 * y) = (x^3 - y^3) - 2023 * (x - y) := by 
      ring 
    rw [eq5] at eq2 
    have eq6 : (x^3 - y^3) - 2023 * (x - y) = (x - y) * (x^2 + x * y + y^2 - 2023) := by 
      rw [eq4] 
      all_goals ring 
    linarith 
  rw [show x^2 + x * y + y^2 - 2023 = (2022 : ℝ) - 2023 by linarith [h2]] at eq3' 
  linarith