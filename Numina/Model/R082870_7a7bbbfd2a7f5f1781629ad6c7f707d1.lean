import Mathlib

theorem calculus_143601 (ε : ℝ) (hε : ε > 0) :
    ∃ δ, δ > 0 ∧ ∀ x, (|x - 10| < δ ∧ x ≠ 10) → |(5 * x ^ 2 - 51 * x + 10) / (x - 10) - 49| < ε := by
  use ε / 5
  constructor
  · -- Show δ > 0
    linarith
  · -- Show that ∀ x, if |x - 10| < δ and x ≠ 10, then |...| < ε
    intro x h
    rcases h with ⟨h1, h2⟩
    have h3 : x - 10 ≠ 0 := by
      intro h'
      apply h2
      linarith
    have h4 : (5 * x ^ 2 - 51 * x + 10) / (x - 10) - 49 = 5 * (x - 10) := by
      field_simp [h3]
      ring_nf
      <;> nlinarith
    rw [h4]
    have h5 : |5 * (x - 10)| = 5 * |x - 10| := by
      rw [abs_mul]
      norm_num
    rw [h5]
    linarith [abs_lt.mp h1, hε]