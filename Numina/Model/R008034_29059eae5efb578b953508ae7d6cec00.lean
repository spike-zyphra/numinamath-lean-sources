import Mathlib

theorem algebra_10421 {n : ℝ} (hn : n ≠ -1 ∧ n ≠ 2) : (2 - n) / (n + 1) + (2 * n - 4) / (2 - n) = 1 ↔ n = -1 / 4 := by
  constructor
  · -- Assume left side, prove right side
    intro h
    have h1 : n + 1 ≠ 0 := by
      intro h2
      apply hn.left
      linarith
    have h2 : 2 - n ≠ 0 := by
      intro h3
      apply hn.right
      linarith
    have eq1 : (2 - n) / (n + 1) + (2 * n - 4) / (2 - n) = 1 := h
    have eq2 : (2 * n - 4) / (2 - n) = -2 := by
      have h2_ne_zero : 2 - n ≠ 0 := h2
      field_simp [h2_ne_zero]
      <;> linarith
    rw [eq2] at eq1
    have eq3 : (2 - n) / (n + 1) = 3 := by
      linarith
    have eq4 : 2 - n = 3 * (n + 1) := by
      have h1_ne_zero : n + 1 ≠ 0 := h1
      field_simp [h1_ne_zero] at eq3 ⊢
      linarith
    linarith
  · -- Assume right side, prove left side
    intro h_eq
    rw [h_eq]
    norm_num