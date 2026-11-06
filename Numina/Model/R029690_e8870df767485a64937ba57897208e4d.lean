import Mathlib

theorem algebra_327174 (θ : ℝ) :
    2 * (Real.cos (2 * θ) + Real.cos θ + 1 / 2) *
    (Real.cos (4 * θ) - Real.cos (3 * θ) + Real.cos θ - 1 / 2) =
    Real.cos (6 * θ) + Real.cos (3 * θ) + 1 / 2 := by
  have h1 : Real.cos (2 * θ) = 2 * Real.cos θ ^ 2 - 1 := by
    rw [Real.cos_two_mul]
  have h2 : Real.cos (3 * θ) = 4 * Real.cos θ ^ 3 - 3 * Real.cos θ := by
    rw [Real.cos_three_mul]
  have h4 : Real.cos (4 * θ) = 8 * Real.cos θ ^ 4 - 8 * Real.cos θ ^ 2 + 1 := by
    have h3 : Real.cos (4 * θ) = 2 * (Real.cos (2 * θ) ) ^ 2 - 1 := by
      have h4 : 4 * θ = 2 * (2 * θ) := by ring
      rw [h4]
      rw [Real.cos_two_mul]
    rw [h3, h1]
    ring
  have h5 : Real.cos (6 * θ) = 32 * Real.cos θ ^ 6 - 48 * Real.cos θ ^ 4 + 18 * Real.cos θ ^ 2 - 1 := by
    have h6 : 6 * θ = 2 * (3 * θ) := by ring
    rw [h6]
    rw [Real.cos_two_mul]
    rw [h2]
    ring_nf
  rw [h1, h4, h2, h5]
  have h6 : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by
    have h7 : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
    linarith
  ring_nf
  <;> simp [h6]
  <;> ring_nf
  <;> simp [h6]
  <;> nlinarith [Real.cos_sq_add_sin_sq θ, sq_nonneg (Real.cos θ ^ 2 - 1), sq_nonneg (Real.sin θ), sq_nonneg (Real.sin θ - 0), sq_nonneg (Real.cos θ - 0)]