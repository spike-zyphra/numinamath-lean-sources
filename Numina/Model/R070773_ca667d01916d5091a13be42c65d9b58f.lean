import Mathlib

open Real
open scoped BigOperators

theorem inequalities_224523 {x : ℕ → ℝ} (hx : ∀ i ∈ Finset.range 3, 0 < x i) :
    3 / 2 ≤ x 0 / (x 1 + x 2) + x 1 / (x 2 + x 0) + x 2 / (x 0 + x 1) := by 
  have h1 : 0 < x 0 := hx 0 (by simp)
  have h2 : 0 < x 1 := hx 1 (by simp)
  have h3 : 0 < x 2 := hx 2 (by simp)
  have h4 : 0 < x 1 + x 2 := by positivity
  have h5 : 0 < x 2 + x 0 := by positivity
  have h6 : 0 < x 0 + x 1 := by positivity
  have h8 : x 0 / (x 1 + x 2) + x 1 / (x 2 + x 0) + x 2 / (x 0 + x 1) - 3 / 2 ≥ 0 := by
    have h9 : x 0 / (x 1 + x 2) + x 1 / (x 2 + x 0) + x 2 / (x 0 + x 1) - 3 / 2 =
      (x 0 * (x 2 + x 0) * (x 0 + x 1) + x 1 * (x 1 + x 2) * (x 0 + x 1) + x 2 * (x 1 + x 2) * (x 2 + x 0) - 3 / 2 * (x 1 + x 2) * (x 2 + x 0) * (x 0 + x 1))
        / ((x 1 + x 2) * (x 2 + x 0) * (x 0 + x 1)) := by 
      field_simp [h4, h5, h6]
      ring
    rw [h9]
    apply div_nonneg
    nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 0 - x 2), sq_nonneg (x 1 - x 2),
      sq_nonneg (x 0 + x 1 - x 2), sq_nonneg (x 0 + x 2 - x 1), sq_nonneg (x 1 + x 2 - x 0),
      mul_pos h1 h2, mul_pos h1 h3, mul_pos h2 h3
    ]
    positivity
  linarith