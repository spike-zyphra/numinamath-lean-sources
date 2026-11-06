import Mathlib

theorem calculus_137103 (ε : ℝ) (hε : ε > 0) :
    ∃ δ, δ > 0 ∧ ∀ x, (|x - 2| < δ ∧ x ≠ 2) → |(3 * x ^ 2 - 5 * x - 2) / (x - 2) - 7| < ε := by
  use ε / 3
  constructor
  · -- show that $\delta > 0$
    linarith
  · -- Now prove the implication for all x
    intro x h
    rcases h with ⟨h1, h2⟩
    have h3 : (3 * x ^ 2 - 5 * x - 2) / (x - 2) = 3 * x + 1 := by
      have h4 : x - 2 ≠ 0 := by
        intro h5
        apply h2
        linarith
      field_simp [h4]
      ring
    rw [h3]
    have h4 : |(3 * x + 1) - 7| = 3 * |x - 2| := by
      have h5 : (3 * x + 1) - 7 = 3 * (x - 2) := by
        ring
      rw [h5]
      rw [abs_mul]
      norm_num
    rw [h4]
    have h5 : |x - 2| < ε / 3 := by
      linarith [h1]
    linarith [h5]