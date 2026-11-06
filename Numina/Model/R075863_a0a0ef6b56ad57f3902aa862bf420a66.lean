import Mathlib

theorem algebra_1213 {x y : ℂ} (h₀ : x + y = 3) (h₁ : x * y = 1) :
    x^5 + y^5 = 123 := by 
  have h2 : x^2 + y^2 = 7 := by 
    calc 
      x^2 + y^2 = (x + y)^2 - 2 * (x * y) := by ring
      _ = 3^2 - 2 * 1 := by rw [h₀, h₁]
      _ = 7 := by norm_num [pow_two]
  
  have h3 : x^3 + y^3 = 18 := by
    calc 
      x^3 + y^3 = (x + y) * ((x^2 + y^2) - (x * y)) := by ring
      _ = 3 * (7 - 1) := by rw [h₀, h2, h₁]
      _ = 18 := by norm_num

  have h4 : x^4 + y^4 = 47 := by 
    calc
      x^4 + y^4 = (x^2 + y^2)^2 - 2 * (x * y)^2 := by ring
      _ = 7^2 - 2 * 1^2 := by rw [h2, h₁]
      _ = 47 := by norm_num [pow_two]

  calc
    x^5 + y^5 = (x + y) * (x^4 + y^4) - (x * y) * (x^3 + y^3) := by ring
    _ = 3 * 47 - 1 * 18 := by rw [h₀, h4, h₁, h3]
    _ = 123 := by norm_num