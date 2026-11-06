import Mathlib

open Real Set

theorem algebra_10681 :
    IsLeast {x | ∃ t : ℝ, x = sqrt (t ^ 2 + 1) + sqrt ((t - 12) ^ 2 + 16)} 13 := by 
  constructor 
  · -- Show that 13 is in the set.
    use 12 / 5
    have h1 : sqrt ((12 / 5 : ℝ) ^ 2 + 1) = 13 / 5 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> linarith
    have h2 : sqrt (( (12 / 5 : ℝ) - 12 ) ^ 2 + 16) = 52 / 5 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> linarith
    rw [h1, h2]
    norm_num
  · -- Show that 13 is the least element in the set.
    intro x hx
    rcases hx with ⟨t, ht⟩
    have h1 : sqrt (t ^ 2 + 1) ≥ 0 := by positivity
    have h2 : sqrt ((t - 12) ^ 2 + 16) ≥ 0 := by positivity
    have h3 : sqrt (t ^ 2 + 1) + sqrt ((t - 12) ^ 2 + 16) ≥ 13 := by
      have h4 : (sqrt (t ^ 2 + 1) + sqrt ((t - 12) ^ 2 + 16)) ^ 2 ≥ 13 ^ 2 := by
        have h5 : (sqrt (t ^ 2 + 1) + sqrt ((t - 12) ^ 2 + 16)) ^ 2 =
            (sqrt (t ^ 2 + 1)) ^ 2 + (sqrt ((t - 12) ^ 2 + 16)) ^ 2 + 2 * (sqrt (t ^ 2 + 1) * sqrt ((t - 12) ^ 2 + 16)) := by ring
        have h6 : (sqrt (t ^ 2 + 1)) ^ 2 = t ^ 2 + 1 := by
          rw [Real.sq_sqrt]
          positivity
        have h7 : (sqrt ((t - 12) ^ 2 + 16)) ^ 2 = (t - 12) ^ 2 + 16 := by
          rw [Real.sq_sqrt]
          positivity
        rw [h5, h6, h7]
        nlinarith [sq_nonneg (sqrt (t ^ 2 + 1) - sqrt ((t - 12) ^ 2 + 16)), sq_nonneg (t - 12 / 5),
          Real.sqrt_nonneg (t ^ 2 + 1), Real.sqrt_nonneg ((t - 12) ^ 2 + 16),
          mul_nonneg (Real.sqrt_nonneg (t ^ 2 + 1)) (Real.sqrt_nonneg ((t - 12) ^ 2 + 16)),
          sq_nonneg (sqrt (t ^ 2 + 1)), sq_nonneg (sqrt ((t - 12) ^ 2 + 16)),
          Real.sq_sqrt (show 0 ≤ (t ^ 2 + 1 : ℝ) by positivity),
          Real.sq_sqrt (show 0 ≤ ((t - 12) ^ 2 + 16 : ℝ) by positivity)
        ]
      nlinarith [Real.sqrt_nonneg (t ^ 2 + 1), Real.sqrt_nonneg ((t - 12) ^ 2 + 16)]
    linarith [ht, h3]