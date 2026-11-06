import Mathlib

open Real Set

theorem inequalities_279604 (θ : ℝ) :
    5 + 8 * cos θ + 4 * cos (2 * θ) + cos (3 * θ) ≥ 0 := by

  have h1 : cos (2 * θ) = 2 * cos θ ^ 2 - 1 := by
    rw [cos_two_mul]

  have h2 : cos (3 * θ) = 4 * cos θ ^ 3 - 3 * cos θ := by
    rw [cos_three_mul]

  rw [h1, h2]

  have h3 : 5 + 8 * cos θ + 4 * (2 * cos θ ^ 2 - 1) + (4 * cos θ ^ 3 - 3 * cos θ) =
      4 * cos θ ^ 3 + 8 * cos θ ^ 2 + 5 * cos θ + 1 := by
    ring

  rw [h3]

  have h4 : 4 * cos θ ^ 3 + 8 * cos θ ^ 2 + 5 * cos θ + 1 =
      (cos θ + 1) * (2 * cos θ + 1) ^ 2 := by
    ring

  rw [h4]

  have h5 : cos θ + 1 ≥ 0 := by
    have h6 : -1 ≤ cos θ := by
      linarith [neg_one_le_cos θ, cos_le_one θ]
    linarith

  have h7 : (2 * cos θ + 1 : ℝ) ^ 2 ≥ 0 := by
    apply sq_nonneg

  have h8 : (cos θ + 1 : ℝ) * ( (2 * cos θ + 1 : ℝ) ^ 2 ) ≥ 0 := by
    apply mul_nonneg
    linarith
    linarith

  linarith