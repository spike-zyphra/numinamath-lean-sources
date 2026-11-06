import Mathlib

open Real Set

theorem calculus_37573 :
    IsLeast {y : ℝ | ∃ x, y = sqrt (x ^ 2 - 6 * x + 13) + sqrt (x ^ 2 - 14 * x + 58)} (sqrt 41) := by
  constructor
  · -- Show that sqrt 41 is in the set
    use 23 / 5
    have h1 : (23 / 5 : ℝ) ^ 2 - 6 * (23 / 5 : ℝ) + 13 = (164 / 25 : ℝ) := by
      norm_num
    have h2 : (23 / 5 : ℝ) ^ 2 - 14 * (23 / 5 : ℝ) + 58 = (369 / 25 : ℝ) := by
      norm_num
    have h3 : sqrt ((23 / 5 : ℝ) ^ 2 - 6 * (23 / 5 : ℝ) + 13) = (2 * sqrt 41) / 5 := by
      rw [h1]
      have h4 : sqrt ((164 / 25 : ℝ)) = (2 * sqrt 41) / 5 := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
        <;> ring_nf <;> norm_num [Real.mul_self_sqrt, Real.sqrt_nonneg]
      rw [h4]
    have h5 : sqrt ((23 / 5 : ℝ) ^ 2 - 14 * (23 / 5 : ℝ) + 58) = (3 * sqrt 41) / 5 := by
      rw [h2]
      have h4 : sqrt ((369 / 25 : ℝ)) = (3 * sqrt 41) / 5 := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
        <;> ring_nf <;> norm_num [Real.mul_self_sqrt, Real.sqrt_nonneg]
      rw [h4]
    rw [h3, h5]
    ring_nf
  · -- Show that sqrt 41 is the least element in the set
    intro y hy
    rcases hy with ⟨x, hx⟩
    have h1 : sqrt (x ^ 2 - 6 * x + 13) = Real.sqrt ((x - 3) ^ 2 + 4) := by
      ring_nf
    have h2 : sqrt (x ^ 2 - 14 * x + 58) = Real.sqrt ((x - 7) ^ 2 + 9) := by
      ring_nf
    have h3 : sqrt (x ^ 2 - 6 * x + 13) + sqrt (x ^ 2 - 14 * x + 58) ≥ Real.sqrt 41 := by
      have h4 : (sqrt (x ^ 2 - 6 * x + 13) + sqrt (x ^ 2 - 14 * x + 58)) ^ 2 ≥ 41 := by
        rw [h1, h2]
        nlinarith [Real.sqrt_nonneg ((x - 3) ^ 2 + 4), Real.sqrt_nonneg ((x - 7) ^ 2 + 9),
                  Real.mul_self_sqrt (show (0 : ℝ) ≤ (x - 3) ^ 2 + 4 by nlinarith),
                  Real.mul_self_sqrt (show (0 : ℝ) ≤ (x - 7) ^ 2 + 9 by nlinarith),
                  sq_nonneg (Real.sqrt ((x - 3) ^ 2 + 4) - 2 * Real.sqrt 41 / 5),
                  sq_nonneg (Real.sqrt ((x - 7) ^ 2 + 9) - 3 * Real.sqrt 41 / 5),
                  Real.sqrt_nonneg ((x - 3) ^ 2 + 4),
                  Real.sqrt_nonneg ((x - 7) ^ 2 + 9),
                  Real.sqrt_nonneg (41 : ℝ),
                  mul_nonneg (Real.sqrt_nonneg ((x - 3) ^ 2 + 4)) (Real.sqrt_nonneg ((x - 7) ^ 2 + 9)),
                  Real.sq_sqrt (show (0 : ℝ) ≤ (41 : ℝ) by norm_num),
                  sq_nonneg ((x - 23 / 5) : ℝ),
                  Real.sq_sqrt (show (0 : ℝ) ≤ (41 : ℝ) by norm_num),
                  mul_nonneg (Real.sqrt_nonneg ((x - 3) ^ 2 + 4)) (Real.sqrt_nonneg ((x - 7) ^ 2 + 9)),
                  Real.sqrt_nonneg (41)
                ]
      have h5 : Real.sqrt 41 ≥ 0 := by positivity
      have h6 : (sqrt (x ^ 2 - 6 * x + 13) + sqrt (x ^ 2 - 14 * x + 58)) ≥ 0 := by positivity
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (41 : ℝ) by norm_num), h4]
    linarith [h3, hx]