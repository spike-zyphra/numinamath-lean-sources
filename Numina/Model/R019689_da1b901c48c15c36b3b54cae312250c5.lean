import Mathlib

theorem algebra_190453 {x : Fin 3 → ℝ} (h₀ : x 0 + x 1 + x 2 = 3) (h₁ : x 0 ^ 3 + x 1 ^ 3 + x 2 ^ 3 = 3) (h₂ : x 0 * x 1 * x 2 = 1) :
    x = ![1, 1, 1] := by
  have h3 : (x 0 - x 1) ^ 2 + (x 0 - x 2) ^ 2 + (x 1 - x 2) ^ 2 = 0 := by
    have eq1 : x 0 ^ 3 + x 1 ^ 3 + x 2 ^ 3 - 3 * (x 0 * x 1 * x 2) = 
        (x 0 + x 1 + x 2) * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 - (x 0 * x 1 + x 0 * x 2 + x 1 * x 2)) := by
      ring
    have eq2 : x 0 ^ 3 + x 1 ^ 3 + x 2 ^ 3 - 3 * (x 0 * x 1 * x 2) = 0 := by
      have h₃ : x 0 ^ 3 + x 1 ^ 3 + x 2 ^ 3 = 3 := h₁
      have h₄ : x 0 * x 1 * x 2 = 1 := h₂
      linarith
    rw [eq1] at eq2
    have eq3 : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 - (x 0 * x 1 + x 0 * x 2 + x 1 * x 2) = 0 := by
      rw [show x 0 + x 1 + x 2 = 3 by linarith] at eq2
      linarith
    nlinarith
  have h4 : x 0 = x 1 := by
    nlinarith
  have h5 : x 0 = x 2 := by
    nlinarith
  have h6 : x 1 = x 2 := by
    nlinarith [h4, h5]
  have h7 : x 0 = 1 := by
    have eq1 : x 0 + x 1 + x 2 = 3 := h₀
    have eq2 : x 1 = x 0 := by linarith [h4]
    have eq3 : x 2 = x 0 := by linarith [h5]
    linarith
  have h8 : x 1 = 1 := by
    linarith [h7, h4]
  have h9 : x 2 = 1 := by
    linarith [h7, h5]
  funext i
  fin_cases i <;> simp [h7, h8, h9]