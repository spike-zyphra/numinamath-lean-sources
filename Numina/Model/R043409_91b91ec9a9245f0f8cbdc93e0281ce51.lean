import Mathlib

theorem calculus_148069 (ε : ℝ) (hε : ε > 0) :
    ∃ δ, δ > 0 ∧ ∀ x, (x ∈ Set.Ioo (-3 - δ) (-3) ∨ x ∈ Set.Ioo (-3) (-3 + δ)) →
    |(2 * x ^ 2 + 5 * x - 3) / (x + 3) + 7| < ε := by 
  use ε / 2 
  constructor 
  · -- Show δ > 0
    linarith 
  · -- Show the implication 
    intro x h 
    rcases h with (h | h)
    · -- Case x ∈ (-3 - δ) (-3)
      rcases h with ⟨hx1, hx2⟩ 
      have h1 : x < -3 := by linarith 
      have h2 : x + 3 < 0 := by linarith 
      have h3 : x + 3 ≠ 0 := by linarith 
      have h4 : (2 * x ^ 2 + 5 * x - 3) / (x + 3) = 2 * x - 1 := by 
        have h5 : x + 3 ≠ 0 := h3 
        field_simp [h5]
        <;> ring 
      rw [h4] 
      have h5 : |(2 * x - 1 + 7)| = |2 * (x + 3)| := by 
        have h6 : 2 * x - 1 + 7 = 2 * (x + 3) := by ring 
        rw [h6] 
      rw [h5]
      have h6 : |2 * (x + 3)| < ε := by 
        have h9 : |2 * (x + 3)| = - (2 * (x + 3)) := by 
          rw [abs_of_neg (show 2 * (x + 3) < 0 by nlinarith)]
          <;> ring 
        rw [h9]
        have h10 : |x + 3| < ε / 2 := by 
          have h11 : x > -3 - ε / 2 := by linarith 
          have h12 : x < -3 := by linarith 
          have h13 : -3 - ε / 2 < -3 := by linarith 
          have h14 : x + 3 < 0 := by linarith 
          have h15 : -(x + 3) < ε / 2 := by nlinarith 
          have h16 : |x + 3| = -(x + 3) := by 
            rw [abs_of_neg (show x + 3 < 0 by linarith)]
          linarith 
        nlinarith [abs_nonneg (x + 3)]
      exact h6 
    · -- Case x ∈ (-3) (-3 + δ)
      rcases h with ⟨hx1, hx2⟩ 
      have h1 : -3 < x := by linarith 
      have h2 : x + 3 > 0 := by linarith 
      have h3 : x + 3 ≠ 0 := by linarith 
      have h4 : (2 * x ^ 2 + 5 * x - 3) / (x + 3) = 2 * x - 1 := by 
        have h5 : x + 3 ≠ 0 := h3 
        field_simp [h5]
        <;> ring 
      rw [h4] 
      have h5 : |(2 * x - 1 + 7)| = |2 * (x + 3)| := by 
        have h6 : 2 * x - 1 + 7 = 2 * (x + 3) := by ring 
        rw [h6] 
      rw [h5] 
      have h6 : |2 * (x + 3)| < ε := by 
        have h9 : |2 * (x + 3)| = 2 * (x + 3) := by 
          rw [abs_of_pos (show 2 * (x + 3) > 0 by nlinarith)]
        rw [h9] 
        have h7 : x + 3 < ε / 2 := by 
          nlinarith [show x < -3 + ε / 2 by linarith]
        nlinarith 
      exact h6