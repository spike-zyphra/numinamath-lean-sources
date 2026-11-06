import Mathlib

theorem inequalities_304393 (a : ℝ) (h : ∀ x ∈ Set.Icc a (a + 2), |x + a| ≥ 2 * |x|) :
    a ≤ -3 / 2 := by
  have h1 := h (a + 2) (by
    constructor <;> linarith
  )
  have h2 : |(a + 2) + a| ≥ 2 * |a + 2| := by
    simpa using h1
  have h3 : |(a + 2) + a| = |2 * (a + 1)| := by
    have h4 : (a + 2) + a = 2 * (a + 1) := by
      ring
    rw [h4]
  rw [h3] at h2
  have h4 : |2 * (a + 1)| = 2 * |a + 1| := by
    have h5 : |2 * (a + 1)| = |(2 : ℝ)| * |a + 1| := by
      rw [abs_mul]
    have h6 : |(2 : ℝ)| = (2 : ℝ) := by
      norm_num [abs_of_nonneg]
    rw [h6] at h5
    linarith
  rw [h4] at h2
  have h5 : |a + 1| ≥ |a + 2| := by
    nlinarith
  have h6 : (a + 1) ^ 2 ≥ (a + 2) ^ 2 := by
    apply sq_le_sq.mpr
    exact h5
  nlinarith