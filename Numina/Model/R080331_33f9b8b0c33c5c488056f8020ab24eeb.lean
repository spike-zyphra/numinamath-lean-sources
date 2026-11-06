import Mathlib

theorem algebra_288718 (x : ℝ) :
    (x^5 + 3 * x^4 + 5 * x^3 + 5 * x^2 + 6 * x + 2 = 0 ∧ x^3 + 3 * x^2 + 4 * x + 1 = 0) ↔
    False := by
  constructor
  · -- Forward direction: if the system of equations then False 
    intro h
    rcases h with ⟨h1, h2⟩

    have eq1 : x^3 = -3 * x^2 - 4 * x - 1 := by linarith

    have eq2 : x^4 = 5 * x^2 + 11 * x + 3 := by
      calc
        x^4 = x * x^3 := by ring
        _ = x * (-3 * x^2 - 4 * x - 1) := by rw [eq1]
        _ = -3 * x^3 - 4 * x^2 - x := by ring
        _ = -3 * (-3 * x^2 - 4 * x - 1) - 4 * x^2 - x := by rw [eq1]
        _ = 5 * x^2 + 11 * x + 3 := by ring

    have eq3 : x^5 = -4 * x^2 - 17 * x - 5 := by
      calc 
        x^5 = x * x^4 := by ring
        _ = x * (5 * x^2 + 11 * x + 3) := by rw [eq2]
        _ = 5 * x^3 + 11 * x^2 + 3 * x := by ring
        _ = 5 * (-3 * x^2 - 4 * x - 1) + 11 * x^2 + 3 * x := by rw [eq1]
        _ = -4 * x^2 - 17 * x - 5 := by ring

    rw [eq3, eq2, eq1] at h1

    have h3 : (x + 1)^2 = 0 := by
      nlinarith

    have h4 : x + 1 = 0 := by 
      nlinarith [sq_nonneg (x + 1)]

    have h5 : x = -1 := by linarith

    rw [h5] at h2

    nlinarith

  · -- Reverse direction: False implies anything
    intro h
    cases h