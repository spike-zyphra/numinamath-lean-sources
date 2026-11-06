import Mathlib

theorem algebra_129944 (a b : ℤ) (h : Odd (a + b)) :
    ∀ n : ℤ, ∃ x y : ℤ, n = x^2 - y^2 + a * x + b * y := by
  intro n
  rcases h with ⟨m, hm⟩
  have h3 : a + b = 2 * m + 1 := by linarith
  use (n - b * m + m ^ 2), (n - b * m + m ^ 2 + m)
  have h4 : a + b - 2 * m = 1 := by
    omega
  have eq1 : (n - b * m + m ^ 2 : ℤ) ^ 2 - (n - b * m + m ^ 2 + m : ℤ) ^ 2 + a * (n - b * m + m ^ 2 : ℤ) + b * (n - b * m + m ^ 2 + m : ℤ) = (a + b - 2 * m : ℤ) * (n - b * m + m ^ 2 : ℤ) + b * m - m ^ 2 := by 
    ring
  have eq2 : (a + b - 2 * m : ℤ) * (n - b * m + m ^ 2 : ℤ) + b * m - m ^ 2 = (n : ℤ) := by 
    have h4' : a + b - 2 * m = 1 := h4
    rw [h4']
    all_goals 
      nlinarith
  nlinarith [eq1, eq2]