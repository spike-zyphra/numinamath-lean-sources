import Mathlib

theorem calculus_144170 (ε : ℝ) (hε : ε > 0) :
    ∃ δ, δ > 0 ∧ ∀ x, (x ∈ Set.Ioo (-7 - δ) (-7) ∨ x ∈ Set.Ioo (-7) (-7 + δ)) →
    |(2 * x ^ 2 + 15 * x + 7) / (x + 7) + 13| < ε := by
  use ε / 2
  constructor
  · -- Show δ > 0
    linarith
  · -- Show the implication for all x
    intro x h
    rcases h with (h | h)
    · -- Case x ∈ (-7 - δ, -7)
      rcases h with ⟨hx1, hx2⟩
      have h1 : x < -7 := by linarith
      have h2 : x + 7 < 0 := by linarith
      have h4 : (2 * x ^ 2 + 15 * x + 7) / (x + 7) = 2 * x + 1 := by
        have h5 : x + 7 < 0 := by linarith
        have h6 : x + 7 ≠ 0 := by linarith
        field_simp [h6]
        ring_nf
        <;> nlinarith
      have h5 : |(2 * x ^ 2 + 15 * x + 7) / (x + 7) + 13| = |(2 * x + 1) + 13| := by
        rw [h4]
      have h6 : |(2 * x + 1) + 13| = |2 * (x + 7)| := by
        ring_nf
      have h7 : |2 * (x + 7)| = 2 * |x + 7| := by
        rw [show 2 * (x + 7) = (2 : ℝ) * (x + 7) by ring]
        rw [abs_mul]
        norm_num
      have h8 : |x + 7| < ε / 2 := by
        have h4 : x + 7 < 0 := by linarith
        have h3 : |x + 7| = -(x + 7) := by
          rw [abs_of_neg]
          all_goals linarith
        linarith
      have h9 : |(2 * x + 1) + 13| < ε := by
        rw [h6, h7]
        linarith [h8]
      rw [h5]
      all_goals linarith
    · -- Case x ∈ (-7, -7 + δ)
      rcases h with ⟨hx1, hx2⟩
      have h1 : x > -7 := by linarith
      have h2 : x + 7 > 0 := by linarith
      have h4 : (2 * x ^ 2 + 15 * x + 7) / (x + 7) = 2 * x + 1 := by
        have h3 : x + 7 > 0 := by linarith
        have h6 : x + 7 ≠ 0 := by linarith
        field_simp [h6]
        ring_nf
        <;> nlinarith
      have h5 : |(2 * x ^ 2 + 15 * x + 7) / (x + 7) + 13| = |(2 * x + 1) + 13| := by
        rw [h4]
      have h6 : |(2 * x + 1) + 13| = |2 * (x + 7)| := by
        ring_nf
      have h7 : |2 * (x + 7)| = 2 * |x + 7| := by
        rw [show 2 * (x + 7) = (2 : ℝ) * (x + 7) by ring]
        rw [abs_mul]
        norm_num
      have h8 : |x + 7| < ε / 2 := by
        have h3 : x + 7 > 0 := by linarith
        have h4 : |x + 7| = x + 7 := by
          rw [abs_of_pos]
          all_goals linarith
        nlinarith
      have h9 : |(2 * x + 1) + 13| < ε := by
        rw [h6, h7]
        linarith [h8]
      rw [h5]
      all_goals linarith