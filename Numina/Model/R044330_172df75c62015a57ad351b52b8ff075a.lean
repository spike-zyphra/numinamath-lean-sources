import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_223632 :
  IsLeast {x | ∃ a b : ℝ, a > 0 ∧ b > 0 ∧ x = ((2*a+2*a*b-b*(b+1))^2 + (b-4*a^2+2*a*(b+1))^2) / (4*a^2+b^2)} 1 := by
  constructor
  · -- Show 1 is in the set
    use 1, 1
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Show 1 is the least
    intro x hx
    rcases hx with ⟨a, b, ha, hb, hx⟩
    have h : ((2*a+2*a*b-b*(b+1))^2 + (b-4*a^2+2*a*(b+1))^2) / (4*a^2+b^2) ≥ 1 := by
      have h1 : 4*a^2+b^2 > 0 := by
        nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb]
      have h2 : (2*a+2*a*b-b*(b+1))^2 + (b-4*a^2+2*a*(b+1))^2 ≥ 4*a^2+b^2 := by
        nlinarith [sq_nonneg (2 * a - b), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (2 * a - b - 1), sq_nonneg (2 * a - b +1), sq_nonneg (a - b), sq_nonneg (4 * a - 2 * b), sq_nonneg (2 * a - 1), sq_nonneg (b - 2), sq_nonneg ((2 * a - b) * (a - 1)), sq_nonneg ((2 * a - b) * (b - 2)), sq_nonneg ((2 * a - 1) * (b - 1)), mul_pos ha hb]
      have h3 : ((2*a+2*a*b-b*(b+1))^2 + (b-4*a^2+2*a*(b+1))^2 : ℝ) / (4*a^2+b^2) ≥ 1 := by
        apply (le_div_iff₀ h1).mpr
        linarith [h2]
      linarith [h3]
    linarith [h, hx]