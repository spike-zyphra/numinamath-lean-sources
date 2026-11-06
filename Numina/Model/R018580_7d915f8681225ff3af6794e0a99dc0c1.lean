import Mathlib

theorem calculus_135187 (ε : ℝ) (hε : ε > 0) :
    ∃ δ, δ > 0 ∧ ∀ x, (x ∈ Set.Ioo (-2 - δ) (-2) ∨ x ∈ Set.Ioo (-2) (-2 + δ)) →
    abs ((3 * x ^ 2 + 5 * x - 2) / (x + 2) + 7) < ε := by
  use ε / 3
  constructor
  · -- Show δ > 0
    linarith
  · -- Show the implication
    intro x h
    rcases h with (h | h)
    · -- Case x ∈ (-2 - δ, -2)
      rcases h with ⟨h1, h2⟩
      have h5 : x + 2 ≠ 0 := by 
        nlinarith
      have h6 : (3 * x ^ 2 + 5 * x - 2) / (x + 2) = 3 * x - 1 := by
        have h5' : x + 2 ≠ 0 := h5
        field_simp [h5']
        ring
      have h7 : ((3 * x ^ 2 + 5 * x - 2) / (x + 2) + 7) = 3 * (x + 2) := by
        rw [h6]
        ring
      rw [h7]
      have h8 : abs (3 * (x + 2)) < ε := by
        have h9 : x + 2 < 0 := by linarith
        have h10 : x + 2 > -ε / 3 := by linarith 
        have h11 : abs (3 * (x + 2)) = - (3 * (x + 2)) := by 
          rw [abs_of_neg]
          nlinarith
          all_goals nlinarith
        rw [h11]
        linarith
      exact h8
    · -- Case x ∈ (-2, -2 + δ)
      rcases h with ⟨h2, h3⟩
      have h5 : x + 2 ≠ 0 := by 
        nlinarith
      have h6 : (3 * x ^ 2 + 5 * x - 2) / (x + 2) = 3 * x - 1 := by
        have h5' : x + 2 ≠ 0 := h5
        field_simp [h5']
        ring
      have h7 : ((3 * x ^ 2 + 5 * x - 2) / (x + 2) + 7) = 3 * (x + 2) := by
        rw [h6]
        ring
      rw [h7]
      have h8 : abs (3 * (x + 2)) < ε := by
        have h9 : x + 2 > 0 := by linarith
        have h10 : x + 2 < ε / 3 := by linarith
        have h11 : abs (3 * (x + 2)) = 3 * (x + 2) := by 
          rw [abs_of_pos]
          nlinarith
        rw [h11]
        linarith
      exact h8