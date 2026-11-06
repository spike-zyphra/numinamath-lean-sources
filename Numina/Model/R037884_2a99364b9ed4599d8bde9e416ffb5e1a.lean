import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_597961 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
  (h : x * y + y * z + z * x = 1) :
  5 / 2 ≤ 1 / (x + y) + 1 / (y + z) + 1 / (z + x) := by
  have h1 : 0 < x + y := by
    by_contra h1
    push_neg at h1
    have h2 : x = 0 := by linarith
    have h3 : y = 0 := by linarith
    rw [h2, h3] at h
    nlinarith
  have h2 : 0 < y + z := by
    by_contra h2
    push_neg at h2
    have h4 : y = 0 := by linarith
    have h5 : z = 0 := by linarith
    rw [h4, h5] at h
    nlinarith
  have h3 : 0 < z + x := by
    by_contra h3
    push_neg at h3
    have h6 : z = 0 := by linarith
    have h7 : x = 0 := by linarith
    rw [h6, h7] at h
    nlinarith
  have h4 : 1 / (x + y) + 1 / (y + z) + 1 / (z + x) ≥ 5 / 2 := by
    have h5 : 0 < (x + y) * (y + z) * (z + x) := by
      positivity
    have h6 : 1 / (x + y) + 1 / (y + z) + 1 / (z + x) - 5 / 2 ≥ 0 := by
      have h7 : 1 / (x + y) + 1 / (y + z) + 1 / (z + x) - 5 / 2 =
          (2 * (y + z) * (z + x) + 2 * (x + y) * (z + x) + 2 * (x + y) * (y + z) - 5 * (x + y) * (y + z) * (z + x)) / (2 * (x + y) * (y + z) * (z + x)) := by
        field_simp
        ring
      rw [h7]
      have h8 : 2 * (y + z) * (z + x) + 2 * (x + y) * (z + x) + 2 * (x + y) * (y + z) - 5 * (x + y) * (y + z) * (z + x) ≥ 0 := by
        nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x + y + z - 2), sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
          h, mul_nonneg hx hy, mul_nonneg hy hz, mul_nonneg hz hx
        ]
      have h9 : 2 * (x + y) * (y + z) * (z + x) > 0 := by
        positivity
      apply div_nonneg
      linarith
      all_goals linarith
    linarith
  linarith