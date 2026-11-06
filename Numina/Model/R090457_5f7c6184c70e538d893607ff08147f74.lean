import Mathlib

theorem calculus_140389 (ε : ℝ) (hε : ε > 0) :
    ∃ δ, δ > 0 ∧ ∀ x, (|x + 6| < δ ∧ x ≠ -6) → |(3 * x ^ 2 + 17 * x - 6) / (x + 6) + 19| < ε := by
  use ε / 3
  constructor
  · -- Show δ > 0
    linarith
  · -- Show that if |x + 6| < δ and x ≠ -6, then |f(x) + 19| < ε
    intro x h
    rcases h with ⟨h1, h2⟩
    have h3 : x + 6 ≠ 0 := by
      intro h4
      apply h2
      linarith
    have h4 : (3 * x ^ 2 + 17 * x - 6) / (x + 6) = 3 * x - 1 := by
      have h5 : x + 6 ≠ 0 := h3
      field_simp [h5]
      <;> ring
    have h5 : |(3 * x ^ 2 + 17 * x - 6) / (x + 6) + 19| = 3 * |x + 6| := by
      rw [h4]
      have h6 : (3 * x - 1 : ℝ) + 19 = 3 * (x + 6) := by ring
      rw [h6]
      simp [abs_mul]
      <;> ring_nf <;> norm_num
    rw [h5]
    linarith [abs_nonneg (x + 6), h1]