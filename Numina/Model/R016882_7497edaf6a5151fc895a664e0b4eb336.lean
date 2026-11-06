import Mathlib

open Real Set

theorem algebra_128345 :
    IsLeast {y : ℝ | ∃ x, y = sqrt (x^2 + 1) + sqrt (x^2 - 4 * x + 8)} (sqrt 13) := by
  constructor
  · -- First part: Show that sqrt 13 is in the set.
    use 2 / 3
    have h1 : Real.sqrt ((2 / 3 : ℝ) ^ 2 + 1) = Real.sqrt (13 / 9 : ℝ) := by
      ring_nf
    have h3 : Real.sqrt ((2 / 3 : ℝ) ^ 2 + 1) = Real.sqrt 13 / 3 := by
      rw [h1]
      have h4 : Real.sqrt (13 / 9 : ℝ) = Real.sqrt 13 / 3 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      linarith [h4]
    have h4 : Real.sqrt ((2 / 3 : ℝ) ^ 2 - 4 * (2 / 3 : ℝ) + 8) = Real.sqrt (52 / 9 : ℝ) := by
      ring_nf
    have h2 : Real.sqrt ((2 / 3 : ℝ) ^ 2 - 4 * (2 / 3 : ℝ) + 8) = 2 * Real.sqrt (13) / 3 := by
      rw [h4]
      have h5 : Real.sqrt (52 / 9 : ℝ) = 2 * Real.sqrt (13) / 3 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
        all_goals norm_num
      linarith [h5]
    rw [h3, h2]
    field_simp
    <;> ring_nf <;> norm_num
  · -- Second part: Show that sqrt 13 is the least element in the set.
    intro y hy
    rcases hy with ⟨x, hx⟩
    rw [hx]
    have h1 : (Real.sqrt (x ^ 2 + 1) + Real.sqrt (x ^ 2 - 4 * x + 8)) ≥ Real.sqrt (13 : ℝ) := by
      have h3 : 0 ≤ (x ^ 2 + 1 : ℝ) := by nlinarith [sq_nonneg x]
      have h4 : 0 ≤ (x ^ 2 - 4 * x + 8 : ℝ) := by
        nlinarith [sq_nonneg (x - 2)]
      have h5 : Real.sqrt (x ^ 2 + 1) ≥ 0 := by positivity
      have h6 : Real.sqrt (x ^ 2 - 4 * x + 8) ≥ 0 := by positivity
      have h6' : (Real.sqrt (x ^ 2 + 1) + Real.sqrt (x ^ 2 - 4 * x + 8)) ^ 2 ≥ (Real.sqrt (13) ) ^ 2 := by
        have h7 : (Real.sqrt (x ^ 2 + 1) + Real.sqrt (x ^ 2 - 4 * x + 8)) ^ 2 =
            (Real.sqrt (x ^ 2 + 1) ) ^ 2 + (Real.sqrt (x ^ 2 - 4 * x + 8) ) ^ 2 + 2 * (Real.sqrt (x ^ 2 + 1) * Real.sqrt (x ^ 2 - 4 * x + 8) ) := by ring
        have h8 : (Real.sqrt (x ^ 2 + 1) ) ^ 2 = (x ^ 2 + 1: ℝ) := Real.sq_sqrt (by linarith [h3])
        have h9 : (Real.sqrt (x ^ 2 - 4 * x + 8) ) ^ 2 = (x ^ 2 - 4 * x + 8: ℝ) := Real.sq_sqrt (by linarith [h4])
        have h10 : (Real.sqrt (13) ) ^ 2 = (13: ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ 13 by norm_num)
        have eq1 : (Real.sqrt (x ^ 2 + 1) + Real.sqrt (x ^ 2 - 4 * x + 8) ) ^ 2 = (x ^ 2 + 1) + (x ^ 2 - 4 * x + 8) + 2 * (Real.sqrt (x ^ 2 + 1) * Real.sqrt (x ^ 2 - 4 * x + 8) ) := by
          rw [h7, h8, h9]
          all_goals ring_nf
        have h13 : (Real.sqrt (13) ) ^ 2 = 13 := Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)
        nlinarith [Real.sqrt_nonneg (x ^ 2 + 1), Real.sqrt_nonneg (x ^ 2 - 4 * x + 8), 
          sq_nonneg (Real.sqrt (x ^ 2 + 1) - Real.sqrt (x ^ 2 - 4 * x + 8) ), 
          sq_nonneg ((x - 2/3) ), sq_nonneg (x - 2/3), 
          sq_nonneg ((x - 1)), sq_nonneg ((x - 2)), 
          Real.sqrt_nonneg (13 : ℝ), 
          mul_nonneg (Real.sqrt_nonneg (x ^ 2 + 1) ) (Real.sqrt_nonneg (x ^ 2 - 4 * x + 8) )
          ]
      nlinarith [Real.sqrt_nonneg (13 : ℝ), Real.sqrt_nonneg (x ^ 2 + 1), Real.sqrt_nonneg (x ^ 2 - 4 * x + 8) ]
    linarith [h1, Real.sqrt_nonneg (13 : ℝ), Real.sqrt_nonneg (x ^ 2 + 1), Real.sqrt_nonneg (x ^ 2 - 4 * x + 8) ]