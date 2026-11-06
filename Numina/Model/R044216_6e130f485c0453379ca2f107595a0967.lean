import Mathlib

theorem algebra_519 : IsLeast {x : ℤ | x > 0 ∧ ∃ y : ℤ, y > 0 ∧ 0.8 = (y / (186 + x : ℝ))} 4 := by
  constructor
  · -- Show that 4 is in the set.
    constructor
    · norm_num
    · use 152
      norm_num
  · -- Show that any x in the set is at least 4.
    intro x hx
    rcases hx with ⟨hx_pos, ⟨y, hy_pos, heq⟩⟩
    by_contra h
    push_neg at h
    have heq2 : (y : ℝ) / (186 + (x : ℝ)) = (0.8 : ℝ) := by
      linarith [heq]
    have heq3 : (y : ℝ) = 0.8 * (186 + (x : ℝ)) := by
      have h_pos : (186 + (x : ℝ)) ≠ 0 := by
        have : x > 0 := hx_pos
        have : (x : ℝ) > (0 : ℝ) := by exact_mod_cast this
        linarith
      field_simp [h_pos] at heq2 ⊢
      linarith [heq2]
    have heq4 : (5 : ℤ) * (y : ℤ) = 744 + 4 * x := by 
      have heq5 : (y : ℝ) = 0.8 * (186 + (x : ℝ)) := heq3
      have heq6 : (y : ℝ) = (4 / 5 : ℝ) * (186 + (x : ℝ)) := by
        rw [heq5]
        norm_num
      have heq7 : (y : ℝ) * 5 = 4 * (186 + (x : ℝ)) := by 
        linarith [heq6]
      have heq8 : (y : ℝ) * 5 = 744 + 4 * (x : ℝ) := by
        nlinarith [heq7]
      have heq9 : (y : ℝ) * 5 = (744 + 4 * x) := by 
        linarith [heq8]
      have heq10 : (y : ℤ) * 5 = 744 + 4 * x := by
        exact_mod_cast heq9
      linarith [heq10]
    have h1 : x < 4 := h
    have h2 : x = 1 ∨ x = 2 ∨ x = 3 := by 
      omega
    rcases h2 with (r | r | r)
    · -- x = 1
      rw [show x = 1 by omega] at heq4
      omega
    · -- x = 2
      rw [show x = 2 by omega] at heq4
      omega
    · -- x = 3
      rw [show x = 3 by omega] at heq4
      omega