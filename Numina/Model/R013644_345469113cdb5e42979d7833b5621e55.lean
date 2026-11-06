import Mathlib

open Real Set

theorem algebra_182985 :
    IsLeast {x | ∃ t : ℝ, x = sqrt (t^2 + 1) + sqrt ((t - 12)^2 + 16)} 13 := by
  constructor
  · -- Show that 13 is in the set.
    use 12 / 5
    have h1 : sqrt ((12 / 5 : ℝ) ^ 2 + 1) = 13 / 5 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h2 : sqrt ((12 / 5 - 12 : ℝ) ^ 2 + 16) = 52 / 5 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1, h2]
    norm_num
  · -- Show that no smaller element is in the set.
    intro x hx
    rcases hx with ⟨t, ht⟩
    have h3 : sqrt (t ^ 2 + 1) + sqrt ((t - 12) ^ 2 + 16) ≥ 13 := by
      have h4 : (sqrt (t ^ 2 + 1) + sqrt ((t - 12) ^ 2 + 16)) ^ 2 ≥ 13 ^ 2 := by
        have h7 : (sqrt (t ^ 2 + 1) + sqrt ((t - 12) ^ 2 + 16)) ^ 2 =
          (sqrt (t ^ 2 + 1)) ^ 2 + (sqrt ((t - 12) ^ 2 + 16)) ^ 2 + 2 * (sqrt (t ^ 2 + 1) * sqrt ((t - 12) ^ 2 + 16)) := by ring
        have h8 : (sqrt (t ^ 2 + 1)) ^ 2 = t ^ 2 + 1 := Real.sq_sqrt (by nlinarith)
        have h9 : (sqrt ((t - 12) ^ 2 + 16)) ^ 2 = (t - 12) ^ 2 + 16 := Real.sq_sqrt (by nlinarith)
        have h10 : (sqrt (t ^ 2 + 1) + sqrt ((t - 12) ^ 2 + 16)) ^ 2 = t ^ 2 + 1 + (t - 12) ^ 2 + 16 + 2 * (sqrt (t ^ 2 + 1) * sqrt ((t - 12) ^ 2 + 16)) := by
          rw [h7, h8, h9]
          all_goals nlinarith
        have h11 : (13 : ℝ) ^ 2 = 169 := by norm_num
        have h12 : t ^ 2 + 1 + (t - 12) ^ 2 + 16 + 2 * (sqrt (t ^ 2 + 1) * sqrt ((t - 12) ^ 2 + 16)) ≥ 169 := by
          nlinarith [sq_nonneg (sqrt (t ^ 2 + 1) - 13 / 5), sq_nonneg (sqrt ((t - 12) ^ 2 + 16) - 52 / 5), 
            mul_nonneg (Real.sqrt_nonneg (t^2 + 1)) (Real.sqrt_nonneg ((t - 12) ^ 2 + 16)), 
            Real.sq_sqrt (show (0 : ℝ) ≤ t^2 + 1 by nlinarith), 
            Real.sq_sqrt (show (0 : ℝ) ≤ (t - 12) ^ 2 + 16 by nlinarith), 
            sq_nonneg (t - 12 / 5), 
            Real.sqrt_nonneg (t ^ 2 + 1), 
            Real.sqrt_nonneg ((t - 12) ^ 2 + 16)
          ]
        linarith [h10, h11, h12]
      have h14 : (sqrt (t ^ 2 + 1) + sqrt ((t - 12) ^ 2 + 16)) ≥ 0 := by positivity
      have h15 : (13 : ℝ) ≥ 0 := by norm_num
      nlinarith [Real.sqrt_nonneg (t ^ 2 + 1), Real.sqrt_nonneg ((t - 12) ^ 2 + 16)]
    linarith [ht, h3]