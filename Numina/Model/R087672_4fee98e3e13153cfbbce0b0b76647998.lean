import Mathlib

theorem algebra_305841 {x : ℚ} (hx : x = -41/9 ∨ x = 130/9) :
    ∃ n, Even n ∧ Even (n + 2) ∧ 9 * x^2 + 23 * x - 2 = n * (n + 2) := by
  rcases hx with (rfl | rfl)
  · use 8
    constructor
    · -- Show that 8 is even
      exact ⟨4, by norm_num⟩
    constructor
    · -- Show that 10 is even
      exact ⟨5, by norm_num⟩
    · -- Show that 9 * (-41/9)^2 + 23 * (-41/9) - 2 = 8 * 10
      norm_num
  · use 46
    constructor
    · -- Show that 46 is even
      exact ⟨23, by norm_num⟩
    constructor
    · -- Show that 48 is even
      exact ⟨24, by norm_num⟩
    · -- Show that 9 * (130/9)^2 + 23 * (130/9) - 2 = 46 * 48
      norm_num