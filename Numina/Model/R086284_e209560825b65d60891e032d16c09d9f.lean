import Mathlib

theorem algebra_6146 {a b c : ℝ} (f : ℝ → ℝ) (h₀ : ∀ x, f x = a * x ^ 2 + b * x + c)
    (h₁ : f (-2) = 8) (h₂ : f 2 = 24) (h₃ : f (-4) = 16) : f 4 = 48 := by
  have eq1 : a * (-2) ^ 2 + b * (-2) + c = 8 := by 
    rw [h₀ (-2)] at h₁ 
    linarith 
  have eq2 : a * 2 ^ 2 + b * 2 + c = 24 := by
    rw [h₀ 2] at h₂ 
    linarith 
  have eq3 : a * (-4) ^ 2 + b * (-4) + c = 16 := by 
    rw [h₀ (-4)] at h₃ 
    linarith 
  have eq4 : f 4 = a * 4 ^ 2 + b * 4 + c := by 
    apply h₀ 
  have eq5 : b = 4 := by
    linarith 
  have eq6 : 4 * a + c = 16 := by 
    rw [eq5] at eq1 
    linarith 
  have eq7 : 16 * a + c = 32 := by 
    rw [eq5] at eq3 
    linarith 
  have eq8 : a = 4 / 3 := by 
    linarith 
  have eq9 : c = 32 / 3 := by 
    rw [eq8] at eq6 
    linarith 
  rw [eq4] 
  rw [eq8, eq5, eq9] 
  norm_num 
  <;> linarith