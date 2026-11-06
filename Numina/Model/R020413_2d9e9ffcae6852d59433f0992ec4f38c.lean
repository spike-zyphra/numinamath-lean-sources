import Mathlib

theorem algebra_242991 {x y z a b c : ℝ} (h₀ : x ≠ 0) (h₁ : y ≠ 0) (h₂ : z ≠ 0)
    (h₃ : a ≠ 0) (h₄ : b ≠ 0) (h₅ : c ≠ 0) (h₆ : x / a + y / b + z / c = 0) (h₇ : a / x + b / y + c / z = 1) :
    a ^ 2 / x ^ 2 + b ^ 2 / y ^ 2 + c ^ 2 / z ^ 2 = 1 := by

  have eq1 : x * b * c + y * a * c + z * a * b = 0 := by 
    field_simp [h₃, h₄, h₅] at h₆ ⊢
    nlinarith
  
  have eq2 : a * y * z + b * x * z + c * x * y = x * y * z := by 
    field_simp [h₀, h₁, h₂] at h₇ ⊢
    nlinarith
  
  have h_eq : a ^ 2 / x ^ 2 + b ^ 2 / y ^ 2 + c ^ 2 / z ^ 2 =
      (a / x + b / y + c / z) ^ 2 - 2 * (a * b / (x * y) + a * c / (x * z) + b * c / (y * z)) := by 
    field_simp [h₃, h₄, h₅, h₀, h₁, h₂]
    ring

  have h_eq2 : a * b / (x * y) + a * c / (x * z) + b * c / (y * z) = (a * b * z + a * c * y + b * c * x) / (x * y * z) := by
    field_simp [h₃, h₄, h₅, h₀, h₁, h₂]
    ring
  
  have h_eq3 : a * b * z + a * c * y + b * c * x = 0 := by 
    linarith
  
  have h_eq4 : a * b / (x * y) + a * c / (x * z) + b * c / (y * z) = 0 := by 
    rw [h_eq2]
    have h_eq5 : x * y * z ≠ 0 := by 
      apply mul_ne_zero
      apply mul_ne_zero
      exact h₀
      exact h₁
      exact h₂
    rw [h_eq3]
    norm_num
    all_goals 
      assumption

  rw [h_eq]
  rw [h₇]
  rw [h_eq4]
  all_goals norm_num