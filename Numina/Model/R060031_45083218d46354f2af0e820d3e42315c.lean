import Mathlib

theorem inequalities_223532 (t : ℝ) : (t + 1) * (1 - abs t) > 0 ↔ t < -1 ∨ t ∈ Set.Ioo (-1) 1 := by
  constructor
  · -- Assume (t + 1) * (1 - abs t) > 0, prove t < -1 ∨ t ∈ Set.Ioo (-1) 1
    intro h
    cases mul_pos_iff.mp h with
    | inl h₁ =>
      have h2 : abs t < 1 := by linarith
      have h3 : -1 < t := by linarith [abs_lt.mp h2]
      have h4 : t < 1 := by linarith [abs_lt.mp h2]
      right
      exact ⟨h3, h4⟩
    | inr h₂ =>
      have h5 : abs t > 1 := by linarith
      cases abs_cases t with
      | inl h6 =>
        linarith
      | inr h7 =>
        left
        linarith
  · -- Assume t < -1 ∨ t ∈ Set.Ioo (-1) 1, prove (t + 1) * (1 - abs t) > 0
    intro h
    cases h with
    | inl h₁ =>
      have h2 : abs t > 1 := by
        rw [abs_of_nonpos (by linarith : t ≤ 0)]
        linarith
      have h4 : (t + 1) < 0 := by linarith
      have h5 : (1 - abs t) < 0 := by linarith
      apply mul_pos_of_neg_of_neg
      all_goals linarith
    | inr h₂ =>
      have h3 : abs t < 1 := by
        cases abs_cases t with
        | inl h4 =>
          have h5 : t < 1 := h₂.2
          linarith
        | inr h4 =>
          have h5 : t > -1 := h₂.1
          linarith
      have h4 : (t + 1) > 0 := by linarith [h₂.1]
      have h5 : (1 - abs t) > 0 := by linarith [h3]
      apply mul_pos
      all_goals linarith