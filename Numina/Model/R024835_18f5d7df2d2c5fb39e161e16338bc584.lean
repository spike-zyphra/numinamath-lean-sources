import Mathlib

theorem algebra_159295 {x y : ℝ} (h₀ : x ≠ 0) (h₁ : y ≠ 0)
    (h₂ : x / y = (x + y) / (2 * x)) (h₃ : x / y ≠ 1) :
    x / y = -1 / 2 := by
  have h4 : x / y = (x + y) / (2 * x) := h₂
  have h5 : x * (2 * x) = y * (x + y) := by
    have eq1 : x / y = (x + y) / (2 * x) := h₂
    field_simp [h₁, h₀] at eq1 ⊢ 
    nlinarith
  have h6 : (2 * x + y) * (x - y) = 0 := by
    linarith [h5]
  cases' (mul_eq_zero.1 h6) with h7 h8
  · -- Case where 2x + y = 0, so y = -2x
    have h8 : y = -2 * x := by 
      linarith
    have h9 : x / y = -1 / 2 := by
      rw [show y = -2 * x by linarith]
      field_simp [h₀]
      <;> nlinarith
    linarith [h9]
  · -- Case where x - y = 0, so x = y
    have h9 : x = y := by 
      linarith
    have h11 : y = x := by
      nlinarith
    have h10 : x / y = 1 := by
      rw [show y = x by linarith]
      field_simp [h₀]
    -- This contradicts h₃ (x / y ≠ 1).
    contradiction