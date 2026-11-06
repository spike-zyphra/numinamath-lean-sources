import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_198962 :
  IsLeast {d | ∃ x y : ℝ, d = sqrt ((x - y)^2 + (5/12 * x - 11 - y^2)^2)} (6311/624) := by
  constructor
  · -- Show that 6311/624 is in the set
    use 33245 / (48 * 169 : ℝ), (5 / 24 : ℝ)
    have h1 : Real.sqrt ((33245 / (48 * 169 : ℝ) - (5 / 24 : ℝ)) ^ 2 + (5 / 12 * (33245 / (48 * 169 : ℝ)) - 11 - (5 / 24 : ℝ) ^ 2) ^ 2) = (6311 / 624 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    linarith [h1]
  · -- Show that 6311/624 is the minimum
    intro d h
    rcases h with ⟨x, y, heq⟩
    have h1 : Real.sqrt ((x - y)^2 + (5/12 * x - 11 - y^2)^2) ≥ (6311 / 624 : ℝ) := by
      have h2 : (x - y)^2 + (5/12 * x - 11 - y^2)^2 ≥ ((6311 / 624 : ℝ) ) ^ 2 := by
        nlinarith [sq_nonneg (x - 33245 / (48 * 169 : ℝ)), sq_nonneg (y - (5 / 24 : ℝ)), sq_nonneg (y - 5 / 24), sq_nonneg (5 / 12 * x - 11 - y^2 - (5 / 12 * (33245 / (48 * 169 : ℝ)) - 11 - (5 / 24 : ℝ) ^ 2)), sq_nonneg (x - y - (33245 / (48 * 169 : ℝ) - (5 / 24 : ℝ))), sq_nonneg (y^2 - (5 / 24 : ℝ) ^ 2), sq_nonneg ((5 / 12 * x - 11 - y^2) - (5 / 12 * (33245 / (48 * 169 : ℝ)) - 11 - (5 / 24 : ℝ) ^ 2)), sq_nonneg (x - 33245 / (48 * 169 : ℝ)), sq_nonneg (y - (5 / 24 : ℝ)), sq_nonneg (y^2 - (5 / 24 : ℝ) ^ 2)]
      have h3 : Real.sqrt ((x - y)^2 + (5/12 * x - 11 - y^2)^2) ≥ Real.sqrt (((6311 / 624 : ℝ) ) ^ 2) := by
        apply Real.sqrt_le_sqrt
        linarith
      have h4 : Real.sqrt (((6311 / 624 : ℝ) ) ^ 2) = (6311 / 624 : ℝ) := by
        rw [Real.sqrt_sq (by norm_num)]
      linarith
    linarith [heq, h1]