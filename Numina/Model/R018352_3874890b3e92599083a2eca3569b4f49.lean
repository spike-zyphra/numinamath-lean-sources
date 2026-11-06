import Mathlib

theorem algebra_305300 (a b : ℝ) (ha : a ≠ 0) (h : ∀ x y, x^2 + y^2 - a * y = 0 → a * x^2 + b * x * y + x = 0 →
    (x = -1 ∧ y = 1) ∨ (x = 1 ∧ y = -1) ∨ (x = 0 ∧ y = 0)) :
    (a^4 - 4 * a * b - 4) * (a * b + 1) = 0 := by
  have h1 := h 0 a (by
    ring
  ) (by 
    ring
  )
  have h2 : (0 = -1 ∧ a = 1) ∨ (0 = 1 ∧ a = -1) ∨ (0 = 0 ∧ a = 0) := by
    simpa using h1
  rcases h2 with (h2 | h2 | h2)
  · 
    exfalso 
    linarith 
  · 
    exfalso
    linarith 
  · 
    exfalso
    have ha0 : a = 0 := by
      linarith
    contradiction