import Mathlib

theorem algebra_3458 {x : ℝ} (hx : x ≠ 0 ∧ x - 1/x = 1) :
    x^4 + 1/x^4 = 7 := by
  rcases hx with ⟨hx1, hx2⟩
  have h1 : x^2 + 1/x^2 = 3 := by 
    have h2 : x - 1/x = 1 := hx2
    calc 
      x^2 + 1/x^2 = (x - 1/x)^2 + 2 := by 
        field_simp
        ring
      _ = 1^2 + 2 := by rw [h2]
      _ = (1 : ℝ) + 2 := by norm_num
      _ = (3 : ℝ) := by norm_num
  have h3 : x^4 + 1/x^4 = 7 := by
    have h4 : x^2 + 1/x^2 = 3 := h1
    calc
      x^4 + 1/x^4 = (x^2 + 1/x^2)^2 - 2 := by 
        field_simp
        ring
      _ = 3^2 - 2 := by rw [h4]
      _ = 9 - 2 := by norm_num
      _ = (7 : ℝ) := by norm_num
  linarith [h3]