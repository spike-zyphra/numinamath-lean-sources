import Mathlib

theorem algebra_122377 {x1 x2 : ℝ} (hx : x1^2 + x1 - 3 = 0 ∧ x2^2 + x2 - 3 = 0)
    (hne : x1 ≠ x2) : x1^3 - 4 * x2^2 + 19 = 0 := by
  rcases hx with ⟨h₁, h₂⟩
  have eq1 : x1^2 + x1 - 3 = 0 := h₁
  have eq2 : x2^2 + x2 - 3 = 0 := h₂
  have h₃ : x1^2 = -x1 + 3 := by
    linarith
  have h₄ : x2^2 = -x2 + 3 := by
    linarith
  have h₅ : x1 + x2 = -1 := by
    have eq3 : x1^2 + x1 - 3 - (x2^2 + x2 - 3) = 0 := by linarith
    have eq4 : (x1 - x2) * (x1 + x2 + 1) = 0 := by
      nlinarith 
    cases' (mul_eq_zero.mp eq4) with h₇ h₈
    · -- Case x1 - x2 = 0, which contradicts hne
      exfalso
      exact hne (by linarith)
    · -- Case x1 + x2 + 1 = 0
      linarith

  have h₆ : x1^3 = 4 * x1 - 3 := by
    calc
      x1^3 = x1 * x1^2 := by ring 
      _ = x1 * (-x1 + 3) := by rw [h₃]
      _ = -x1^2 + 3 * x1 := by ring 
      _ = -(-x1 + 3) + 3 * x1 := by rw [h₃]
      _ = 4 * x1 - 3 := by ring 
  have h₇ : x2^2 = -x2 + 3 := h₄
  
  nlinarith [h₅, h₆, h₄]