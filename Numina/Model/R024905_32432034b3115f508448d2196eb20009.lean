import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_42258 :
  IsGreatest {y : ℝ | ∃ x : ℝ, x ≠ 0 ∧ y = ((x^2 + 5 * x + 12) * (x^2 + 5 * x - 12) *
    (x^2 - 5 * x + 12) * (-x^2 + 5 * x + 12)) / x^4} 576 := by
  constructor
  · -- Show that 576 is attained when x = 3.
    use 3
    constructor
    · -- Show 3 is not 0
      norm_num
    · -- Compute the value at x = 3
      norm_num
  · -- Show no greater element exists
    intro y
    rintro ⟨x, hx, hy⟩
    have h1 : ((x^2 + 5 * x + 12) * (x^2 + 5 * x - 12) * (x^2 - 5 * x + 12) * (-x^2 + 5 * x + 12)) / x^4 ≤ 576 := by 
      have h4 : x ^ 4 > 0 := by
        have h5 : x ≠ 0 := hx
        positivity
      have h3 : (x ^ 2 + 5 * x + 12) * (x ^ 2 + 5 * x - 12) * (x ^ 2 - 5 * x + 12) * (-x ^ 2 + 5 * x + 12) ≤ 576 * x ^ 4 := by
        nlinarith [sq_nonneg (x ^ 2 - 9), sq_nonneg (x * 3 - 3), sq_nonneg (x - 2), sq_nonneg (x - 3), sq_nonneg (x - 4), sq_nonneg (x + 1), sq_nonneg (x + 3), sq_nonneg (x + 4), sq_nonneg (x ^ 2 - 4), sq_nonneg (x ^ 2 - 9), sq_nonneg (x ^ 2 - 16), sq_nonneg (x ^ 2 + 5 * x), sq_nonneg (x ^ 2 - 5 * x)]
      apply (div_le_iff₀ h4).mpr 
      linarith
    have h2 : y = ((x^2 + 5 * x + 12) * (x^2 + 5 * x - 12) * (x^2 - 5 * x + 12) * (-x^2 + 5 * x + 12)) / x^4 := by 
      linarith
    linarith [h1, h2]