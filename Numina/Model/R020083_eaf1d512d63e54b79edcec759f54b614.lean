import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_188248 :
  IsLeast {d | ∃ x, d = sqrt ((x - 0)^2 + (x^4 / 8 - 5 / 2)^2)} (sqrt 17 / 2) := by
  constructor
  · -- Show that `sqrt 17 / 2` is in the set.
    use 2
    have h1 : sqrt ((2 - (0 : ℝ)) ^ 2 + (2 ^ 4 / 8 - 5 / 2) ^ 2) = sqrt 17 / 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    linarith [h1]
  · -- Show that `sqrt 17 / 2` is the least element in the set.
    intro d hd
    rcases hd with ⟨x, hx⟩
    have h2 : d = sqrt ((x - (0 : ℝ)) ^ 2 + (x^4 / 8 - 5 / 2) ^ 2) := by linarith
    have h3 : (x - 0 : ℝ) ^ 2 + (x^4 / 8 - 5 / 2) ^ 2 ≥ 17 / 4 := by
      nlinarith [sq_nonneg (x ^ 2 - 4), sq_nonneg (x ^ 2 - 2), sq_nonneg (x ^ 4 - 16),
        sq_nonneg (x ^ 2 + 2), sq_nonneg ((x ^ 2 - 2) * (x ^ 2 + 2)), sq_nonneg ((x ^ 2 - 4) * (x ^ 4 - 16)), sq_nonneg (x ^ 2 - 4), sq_nonneg (x ^ 2 - 2)]
    have h4 : sqrt ((x - (0 : ℝ)) ^ 2 + (x ^ 4 / 8 - 5 / 2) ^ 2) ≥ sqrt (17 / 4) := by
      apply Real.sqrt_le_sqrt
      linarith [h3]
    have h5 : sqrt (17 / 4) = sqrt 17 / 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    have h6 : sqrt ((x - (0 : ℝ)) ^ 2 + (x ^ 4 / 8 - 5 / 2) ^ 2) ≥ sqrt 17 / 2 := by
      rw [h5] at h4
      linarith
    rw [h2]
    linarith [h6]