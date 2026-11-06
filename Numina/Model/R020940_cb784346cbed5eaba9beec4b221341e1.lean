import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_13892 (f : ℝ → ℝ) (hf : f = λ x => 4 * x + 1 / x ^ 4) :
    IsLeast {y | ∃ x > 0, f x = y} 5 := by
  constructor
  · -- 5 is in the set
    use 1
    constructor
    · norm_num
    · -- Show f(1) = 5
      rw [hf]
      norm_num
  · -- Show 5 is the least element in the set
    intro y hy
    rcases hy with ⟨x, hx, hfx⟩
    rw [hf] at hfx
    have h1 : 4 * x + 1 / x ^ 4 ≥ 5 := by
      have h2 : x > 0 := hx
      have h3 : 4 * x + 1 / x ^ 4 - 5 ≥ 0 := by
        have h4 : 4 * x + 1 / x ^ 4 - 5 = (4 * x ^ 5 + 1 - 5 * x ^ 4) / x ^ 4 := by
          field_simp
          <;> ring
        rw [h4]
        have h5 : x ^ 4 > 0 := by positivity
        have h6 : 4 * x ^ 5 - 5 * x ^ 4 + 1 ≥ 0 := by
          nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 2 - x), sq_nonneg (x ^ 2 - 2 * x), sq_nonneg (x - 1), sq_nonneg (x ^ 4 - 1), sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 2 - x^ 2), sq_nonneg (x * (x - 1)), sq_nonneg ((x) ^2 - (x)), sq_nonneg (x - 1), sq_nonneg (x ^2 - 1), sq_nonneg (x ^2 - x), sq_nonneg (x^2 - x^2), sq_nonneg (x * (x - 1)), mul_pos hx hx]
        have h7 : (4 * x ^ 5 + 1 - 5 * x ^ 4) ≥ 0 := by
          nlinarith
        apply div_nonneg
        linarith
        positivity
      linarith
      all_goals linarith
    have h4 : (4 * x + 1 / x ^ 4) = y := by
      simpa using hfx
    linarith
    all_goals linarith