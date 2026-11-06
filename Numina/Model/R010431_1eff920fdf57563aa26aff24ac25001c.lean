import Mathlib

theorem algebra_9010 (a : ℝ) : (∃ x y, x - y = a + 3 ∧ 2 * x + y = 5 * a ∧ x < y) ↔ a < -3 := by
  constructor
  · rintro ⟨x, y, h1, h2, h3⟩
    have eq1 : x = 2 * a + 1 := by 
      linarith
    have eq2 : y = a - 2 := by 
      linarith [h1, eq1]
    linarith [eq1, eq2, h3]
  · intro ha
    use 2 * a + 1, a - 2
    constructor
    · linarith 
    constructor
    · linarith
    · linarith