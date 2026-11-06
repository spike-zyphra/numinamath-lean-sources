import Mathlib

theorem algebra_224512 {a b c : ℝ} (h₀ : a ≠ 0) (h₁ : b ≠ 0) (h₂ : c ≠ 0)
    (h₃ : a + b + c = 0) :
    a * (1 / b + 1 / c) + b * (1 / a + 1 / c) + c * (1 / a + 1 / b) = -3 := by 
  have eq1 : a + b + c = 0 := h₃
  have eq2 : a + c = -b := by 
    linarith 
  have eq3 : a + b = -c := by 
    linarith 
  have eq4 : b + c = -a := by 
    linarith 
  have eq5 : a * (1 / b + 1 / c) + b * (1 / a + 1 / c) + c * (1 / a + 1 / b) = (a + c) / b + (a + b) / c + (b + c) / a := by 
    field_simp [h₁, h₂, h₀]
    ring 
  rw [eq5]
  have eq6 : (a + c) / b = -1 := by 
    rw [show a + c = -b by linarith]
    field_simp [h₁]
  have eq7 : (a + b) / c = -1 := by
    rw [show a + b = -c by linarith]
    field_simp [h₂]
  have eq8 : (b + c) / a = -1 := by
    rw [show b + c = -a by linarith]
    field_simp [h₀]
  rw [eq6, eq7, eq8]
  norm_num