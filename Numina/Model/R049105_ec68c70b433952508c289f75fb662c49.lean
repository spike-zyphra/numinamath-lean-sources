import Mathlib

theorem calculus_127366 (ε : ℝ) (hε : ε > 0) :
    ∃ δ, δ > 0 ∧ ∀ x, (x ∈ Set.Ioo (-5 - δ) (-5) ∨ x ∈ Set.Ioo (-5) (-5 + δ)) →
    abs ((x ^ 2 + 2 * x - 15) / (x + 5) + 8) < ε := by
  use ε
  constructor
  · -- Show that δ = ε is positive
    exact hε
  · -- Now we need to prove that for all x, if x approaches -5 within δ, then |f(x)+8| < ε
    intro x h
    cases h with
    | inl h₁ =>
      rcases h₁ with ⟨h₁₁, h₁₂⟩
      have h1 : x + 5 < 0 := by linarith
      have h3 : x + 5 ≠ 0 := by linarith
      have h4 : (x ^ 2 + 2 * x - 15) / (x + 5) = x - 3 := by
        have h5 : x + 5 ≠ 0 := by linarith
        field_simp [h5]
        ring
      have h5 : (x ^ 2 + 2 * x - 15) / (x + 5) + 8 = (x + 5) := by
        rw [h4]
        ring
      have h6 : abs ((x ^ 2 + 2 * x - 15) / (x + 5) + 8) = abs ((x + 5) : ℝ) := by
        rw [h5]
      rw [h6]
      have h7 : abs ((x + 5) : ℝ) = -(x + 5) := by
        rw [abs_of_nonpos]
        linarith
        all_goals linarith
      rw [h7]
      have h8 : x + 5 > -ε := by linarith
      linarith
    | inr h₂ =>
      rcases h₂ with ⟨h₂₁, h₂₂⟩
      have h1 : x + 5 > 0 := by linarith
      have h3 : x + 5 ≠ 0 := by linarith
      have h4 : (x ^ 2 + 2 * x - 15) / (x + 5) = x - 3 := by
        have h5 : x + 5 ≠ 0 := by linarith
        field_simp [h5]
        ring
      have h5 : (x ^ 2 + 2 * x - 15) / (x + 5) + 8 = (x + 5) := by
        rw [h4]
        ring
      have h6 : abs ((x ^ 2 + 2 * x - 15) / (x + 5) + 8) = abs ((x + 5) : ℝ) := by
        rw [h5]
      rw [h6]
      have h7 : abs ((x + 5) : ℝ) = x + 5 := by
        rw [abs_of_pos]
        linarith
        all_goals linarith
      rw [h7]
      have h8 : x + 5 < ε := by linarith
      linarith