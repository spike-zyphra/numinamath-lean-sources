import Mathlib

theorem calculus_122734 (ε : ℝ) (hε : ε > 0) :
    ∃ δ, δ > 0 ∧ ∀ x, (x ∈ Set.Ioo (1 / 3 - δ) (1 / 3) ∨ x ∈ Set.Ioo (1 / 3) (1 / 3 + δ)) →
    |(6 * x ^ 2 + x - 1) / (x - 1 / 3) - 5| < ε := by 
  use ε / 6
  constructor
  · -- Proof that δ > 0 given ε > 0
    linarith
  · -- Proof of the implication
    intro x
    intro h
    rcases h with (h | h)
    · -- Case where x ∈ (1/3 - δ, 1/3)
      rcases h with ⟨h1, h2⟩
      have h3 : x - 1 / 3 ≠ 0 := by linarith
      have h4 : (6 * x ^ 2 + x - 1) / (x - 1 / 3) = 6 * x + 3 := by
        have h5 : (6 * x ^ 2 + x - 1) = (2 * x + 1) * (3 * x - 1) := by ring_nf
        rw [h5]
        have h6 : x - 1 / 3 = (3 * x - 1) / 3 := by ring_nf
        rw [h6]
        have h7 : (3 * x - 1) ≠ 0 := by
          intro h8
          have h9 : 3 * x = 1 := by linarith [h8]
          have h10 : x = 1 / 3 := by linarith [h9]
          linarith
        field_simp [h7]
        <;> ring_nf <;> tauto
      rw [h4]
      have h6 : |(6 * x + 3) - 5| = 6 * |x - 1 / 3| := by
        have h71 : (6 * x + 3) - 5 = 6 * (x - 1 / 3) := by ring_nf
        rw [h71]
        rw [abs_mul]
        norm_num
        all_goals linarith
      have h8 : |x - 1 / 3| < ε / 6 := by
        have h9 : x - 1 / 3 < 0 := by linarith
        have h10 : |x - 1 / 3| = (1 / 3 - x) := by
          rw [abs_of_neg (show x - 1 / 3 < 0 by linarith)]
          all_goals linarith
        rw [h10]
        linarith
      linarith [h6, h8]
    · -- Case where x ∈ (1/3, 1/3 + δ)
      rcases h with ⟨h1, h2⟩
      have h3 : x - 1 / 3 ≠ 0 := by linarith
      have h4 : (6 * x ^ 2 + x - 1) / (x - 1 / 3) = 6 * x + 3 := by
        have h5 : (6 * x ^ 2 + x - 1) = (2 * x + 1) * (3 * x - 1) := by ring_nf
        rw [h5]
        have h6 : x - 1 / 3 = (3 * x - 1) / 3 := by ring_nf
        rw [h6]
        have h7 : (3 * x - 1) ≠ 0 := by
          intro h8
          have h9 : 3 * x = 1 := by linarith [h8]
          have h10 : x = 1 / 3 := by linarith [h9]
          linarith
        field_simp [h7]
        <;> ring_nf <;> tauto
      rw [h4]
      have h6 : |(6 * x + 3) - 5| = 6 * |x - 1 / 3| := by
        have h71 : (6 * x + 3) - 5 = 6 * (x - 1 / 3) := by ring_nf
        rw [h71]
        rw [abs_mul]
        norm_num
        all_goals linarith
      have h8 : |x - 1 / 3| < ε / 6 := by
        have h12 : x - 1 / 3 > 0 := by linarith
        have h13 : |x - 1 / 3| = x - 1 / 3 := by
          rw [abs_of_pos (show x - 1 / 3 > 0 by linarith)]
        rw [h13]
        linarith
      linarith [h6, h8]