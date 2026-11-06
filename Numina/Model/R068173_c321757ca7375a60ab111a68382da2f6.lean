import Mathlib

theorem algebra_293064 (a b c : ℝ) (h₀ : a * 1 + b * 2 + c * 1 * 2 = 3) (h₁ : a * 2 + b * 3 + c * 2 * 3 = 4)
    (d : ℝ) (hd : d ≠ 0) (h₂ : ∀ x, a * x + b * d + c * x * d = x) :
    d = 4 := by
  have eq1 := h₂ 0
  have eq2 : b * d = 0 := by
    nlinarith
  
  have hb : b = 0 := by
    apply_fun (fun x => x / d) at eq2
    field_simp [hd] at eq2
    linarith

  have eq3 := h₂ 1
  rw [hb] at eq3
  have eq4 : a + c * d = 1 := by
    nlinarith
  
  have eq5 : a + 2 * c = 3 := by
    rw [hb] at h₀
    linarith
  
  have eq6 : 2 * a + 6 * c = 4 := by
    rw [hb] at h₁
    linarith
  
  have eq7 : c = -1 := by
    nlinarith [eq5, eq6]

  have eq8 : a = 5 := by
    rw [eq7] at eq5
    linarith

  rw [eq8, eq7] at eq4 
  nlinarith