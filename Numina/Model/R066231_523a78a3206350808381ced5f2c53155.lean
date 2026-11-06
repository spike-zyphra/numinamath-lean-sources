import Mathlib

theorem algebra_313404 {a b c d : ℝ} (f : ℝ → ℝ)
    (h₀ : f = fun x => x^4 + a * x^3 + b * x^2 + c * x + d)
    (h₁ : f 1 = 0) (h₂ : f 2 = 0) (h₃ : f 3 = 0) :
    f 0 + f 4 = 24 := by 
  have eq1 : 1^4 + a * 1^3 + b * 1^2 + c * 1 + d = 0 := by 
    rw [h₀] at h₁ 
    simpa using h₁ 
  have eq2 : 2^4 + a * 2^3 + b * 2^2 + c * 2 + d = 0 := by 
    rw [h₀] at h₂ 
    simpa using h₂ 
  have eq3 : 3^4 + a * 3^3 + b * 3^2 + c * 3 + d = 0 := by 
    rw [h₀] at h₃ 
    simpa using h₃ 
  simp [h₀]
  <;> nlinarith [eq1, eq2, eq3]