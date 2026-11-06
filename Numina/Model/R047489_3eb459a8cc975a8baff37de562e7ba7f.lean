import Mathlib
theorem number_theory_609455 : IsLeast {b : ℕ | b > 1 ∧ IsSquare (1 * b ^ 3 + 1 * b ^ 2 + 1 * b + 1 * b ^ 0)} 7:= by
  constructor
  · -- Show 7 is in the set
    constructor
    · -- Show 7 > 1
      norm_num
    · -- Show that $1111_{7}$ is a perfect square
      native_decide
  · -- Show 7 is the smallest 
    intro b hb
    rcases hb with ⟨hb1, h2⟩
    by_contra h
    push_neg at h
    have h3 : b < 7 := h
    have h4 : b > 1 := hb1
    have h5 : b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 := by
      interval_cases b <;> omega
    rcases h5 with (rfl | rfl | rfl | rfl | rfl)
    · -- b = 2
      exfalso
      have h2' : ¬IsSquare (1 * 2 ^ 3 + 1 * 2 ^ 2 + 1 * 2 + 1 * 2 ^ 0) := by 
        native_decide
      have h3 : IsSquare (1 * 2 ^ 3 + 1 * 2 ^ 2 + 1 * 2 + 1 * 2 ^ 0) := h2
      exact h2' h3
    · -- b = 3
      exfalso 
      have h2' : ¬IsSquare (1 * 3 ^ 3 + 1 * 3 ^ 2 + 1 * 3 + 1 * 3 ^ 0) := by 
        native_decide
      have h3 : IsSquare (1 * 3 ^ 3 + 1 * 3 ^ 2 + 1 * 3 + 1 * 3 ^ 0) := h2
      exact h2' h3
    · -- b = 4
      exfalso 
      have h2' : ¬IsSquare (1 * 4 ^ 3 + 1 * 4 ^ 2 + 1 * 4 + 1 * 4 ^ 0) := by
        native_decide
      have h3 : IsSquare (1 * 4 ^ 3 + 1 * 4 ^ 2 + 1 * 4 + 1 * 4 ^ 0) := h2
      exact h2' h3
    · -- b = 5
      exfalso 
      have h2' : ¬IsSquare (1 * 5 ^ 3 + 1 * 5 ^ 2 + 1 * 5 + 1 * 5 ^ 0) := by 
        native_decide
      have h3 : IsSquare (1 * 5 ^ 3 + 1 * 5 ^ 2 + 1 * 5 + 1 * 5 ^ 0) := h2
      exact h2' h3
    · -- b = 6
      exfalso 
      have h2' : ¬IsSquare (1 * 6 ^ 3 + 1 * 6 ^ 2 + 1 * 6 + 1 * 6 ^ 0) := by
        native_decide 
      have h3 : IsSquare (1 * 6 ^ 3 + 1 * 6 ^ 2 + 1 * 6 + 1 * 6 ^ 0) := h2
      exact h2' h3