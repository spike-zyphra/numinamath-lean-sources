import Mathlib

theorem algebra_285961 {x y : ℝ} (h₀ : (x + y) ^ 4 + (x - y) ^ 4 = 4112) (h₁ : x ^ 2 - y ^ 2 = 16) :
    x ^ 2 + y ^ 2 = 34 := by
  have eq1 : (x + y) ^ 4 + (x - y) ^ 4 = 2 * (x^4 + 6 * x^2 * y^2 + y^4) := by
    ring
  rw [eq1] at h₀ 
  have eq2 : x^2 = y^2 + 16 := by 
    linarith
  have eq3 : x^4 + 6 * x^2 * y^2 + y^4 = 2056 := by 
    nlinarith
  have h4 : x^4 + 6 * x^2 * y^2 + y^4 = 8 * (y^2)^2 + 128 * (y^2) + 256 := by 
    have h5 : x^2 = y^2 + 16 := eq2
    have eq5 : x^4 = (x^2) ^ 2 := by ring
    rw [eq5, h5]
    all_goals 
      ring_nf <;> nlinarith
  rw [h4] at eq3
  have h5 : (y^2) = 9 := by 
    nlinarith [sq_nonneg (y^2 - 9), sq_nonneg (y^2 + 25)]
  have h6 : y^2 = 9 := by 
    nlinarith 
  have eq4 : x^2 = 25 := by 
    nlinarith [h₁, h6]
  have h7 : x^2 + y^2 = 34 := by 
    nlinarith
  exact h7