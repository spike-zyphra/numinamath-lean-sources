import Mathlib

theorem number_theory_22806 {a b : ℤ} (h₀ : a ≥ b) (h₁ : (a + b) % 10 = 2) (h₂ : (2 * a + b) % 10 = 1) :
    (a - b) % 10 = 6 := by
  have eq1 : (a + b) % 10 = 2 := h₁
  have eq2 : (2 * a + b) % 10 = 1 := h₂
  have eq3 : (a - b) % 10 = 6 := by
    omega
  exact eq3