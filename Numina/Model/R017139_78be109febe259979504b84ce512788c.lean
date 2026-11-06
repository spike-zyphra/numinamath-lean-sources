import Mathlib

theorem calculus_130712 (ε : ℝ) (hε : ε > 0) :
    ∃ δ, δ > 0 ∧ ∀ x, (x ∈ Set.Ioo (-1 / 3 - δ) (-1 / 3) ∨ x ∈ Set.Ioo (-1 / 3) (-1 / 3 + δ)) →
    abs ((3 * x ^ 2 - 2 * x - 1) / (x + 1 / 3) + 4) < ε := by 
  use ε / 3
  constructor
  · -- Show that δ is positive
    linarith
  · -- Show the implication
    intro x h
    cases h with
    | inl h =>
      have h1 : x ∈ Set.Ioo (-1 / 3 - ε / 3) (-1 / 3) := h
      rcases h1 with ⟨ha, hb⟩
      have eq1 : (3 * x ^ 2 - 2 * x - 1) / (x + 1 / 3) + 4 = 3 * x + 1 := by
        have h1' : (3 * x + 1) ≠ 0 := by 
          nlinarith
        have h2 : (3 * x ^ 2 - 2 * x - 1) = (3 * x + 1) * (x - 1) := by
          nlinarith 
        have h3 : (x + 1/3) = (3 * x + 1) / 3 := by 
          field_simp 
          <;> ring_nf 
        rw [h2, h3] 
        -- Show that ( (3 * x + 1) * (x - 1) ) / ( (3 * x + 1) / 3 ) = 3 * (x - 1)
        have h6 : (3 * x + 1) ≠ 0 := by 
          nlinarith 
        field_simp [h6] 
        <;> ring_nf 
        <;> field_simp [h6] 
        <;> nlinarith 
        all_goals linarith
      rw [eq1]
      have h4 : -ε < 3 * x + 1 := by 
        linarith 
      have h5 : 3 * x + 1 < 0 := by 
        nlinarith 
      rw [abs_of_neg (by linarith)]
      linarith 
    | inr h => 
      have h1 : x ∈ Set.Ioo (-1 / 3) (-1 / 3 + ε / 3) := h
      rcases h1 with ⟨hb, hc⟩
      have eq1 : (3 * x ^ 2 - 2 * x - 1) / (x + 1 / 3) + 4 = 3 * x + 1 := by
        have h1' : (3 * x + 1) ≠ 0 := by 
          nlinarith 
        have h2 : (3 * x ^ 2 - 2 * x - 1) = (3 * x + 1) * (x - 1) := by
          nlinarith 
        have h3 : (x + 1/3) = (3 * x + 1) / 3 := by 
          field_simp 
          <;> ring_nf 
        rw [h2, h3]
        have h6 : (3 * x + 1) ≠ 0 := by 
          nlinarith 
        field_simp [h6] 
        <;> ring_nf 
        <;> field_simp [h6] 
        <;> nlinarith 
        all_goals nlinarith 
      rw [eq1]
      have h4 : 0 < 3 * x + 1 := by 
        linarith 
      have h5 : 3 * x + 1 < ε := by 
        nlinarith 
      rw [abs_of_pos (by linarith)]
      linarith
      all_goals linarith 
  all_goals linarith