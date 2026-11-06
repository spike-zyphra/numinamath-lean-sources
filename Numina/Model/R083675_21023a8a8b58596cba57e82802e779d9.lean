import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_12343 :
  IsLeast {y : ℝ | ∃ x > 0, y = x^2 + 8 * x + 64 / x^3} 28 := by
  constructor
  · -- Show that 28 belongs to the set, witness x = 2
    use 2
    constructor
    · -- Show that 2 > 0
      norm_num
    · -- Show that 28 = 2^2 + 8 * 2 + 64 / 2^3
      norm_num
  · -- Show that 28 is the least element in the set
    intro y hy
    rcases hy with ⟨x, hx, h_eq⟩
    have h1 : x ^ 2 + 8 * x + 64 / x ^ 3 ≥ 28 := by
      have h2 : x ^ 5 + 8 * x ^ 4 - 28 * x ^ 3 + 64 ≥ 0 := by
        nlinarith [sq_nonneg (x ^ 2 - 2 * x) , sq_nonneg (x - 2), sq_nonneg (x + 2), sq_nonneg (x ^ 2 - 4), sq_nonneg (x ^ 2 - 4 * x + 4), sq_nonneg (x * (x - 2)), sq_nonneg ((x - 2) * (x + 2)), sq_nonneg (x ^ 2 - 4 * x - 2), sq_nonneg (x * (x ^ 2 - 4)), mul_nonneg (show 0 ≤ x from by linarith) (show 0 ≤ x ^ 2 from by nlinarith)]
      have h3_pos1 : x ^ 3 > 0 := by
        positivity
      have h4 : x ^ 2 + 8 * x + 64 / x ^ 3 - 28 ≥ 0 := by
        have h5 : (x ^ 2 + 8 * x + 64 / x ^ 3 - 28) = (x ^ 5 + 8 * x ^ 4 - 28 * x ^ 3 + 64) / (x ^ 3) := by
          field_simp
          ring
        rw [h5]
        have h6_pos1 : (x ^ 3) > 0 := by
          positivity
        have h2_pos1 : x ^ 5 + 8 * x ^ 4 - 28 * x ^ 3 + 64 ≥ 0 := by linarith
        apply div_nonneg (show 0 ≤ (x ^ 5 + 8 * x ^ 4 - 28 * x ^ 3 + 64 : ℝ) by linarith) (show 0 ≤ (x ^ 3 : ℝ) by positivity)
      linarith
    have h4 : y ≥ 28 := by
      rw [h_eq]
      linarith [h1]
    linarith