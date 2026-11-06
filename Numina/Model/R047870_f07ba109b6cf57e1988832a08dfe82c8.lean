import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_18853 : {x : ℝ | x^4 + 4 * x^2 ∈ Ioo (-4) 21} = Ioo (-sqrt 3) (sqrt 3) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_Ioo]
  constructor
  · -- Assume x in {x : ℝ | x^4 + 4 * x^2 ∈ Ioo (-4) 21}, need to show in Ioo (-sqrt 3) (sqrt 3)
    rintro ⟨h₁, h₂⟩
    have h3 : x^4 + 4 * x^2 ≥ 0 := by
        nlinarith [sq_nonneg (x^2), sq_nonneg (x)]
    have h4 : x^4 + 4 * x^2 < 21 := by linarith
    -- Show x^2 < 3
    have h5 : x^2 < 3 := by
      nlinarith [sq_nonneg (x^2 - 3), sq_nonneg (x^2 + 4), sq_nonneg (x), sq_nonneg (x - 0)]
    have h6 : -sqrt 3 < x := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), sq_nonneg (x + sqrt 3), h5]
    have h7 : x < sqrt 3 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), sq_nonneg (x - sqrt 3), h5]
    constructor <;> linarith
  · -- Assume in Ioo (-sqrt 3) (sqrt 3), need to show {x : ℝ | x^4 + 4 * x^2 ∈ Ioo (-4) 21}
    rintro ⟨h₁, h₂⟩
    -- Show x^4 + 4 * x^2 < 21
    have h4 : x^2 < 3 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), sq_nonneg (x + sqrt 3), sq_nonneg (x - sqrt 3)]
    -- Show both parts of the interval
    constructor
    · -- Show -4 < x^4 + 4 * x^2
      have h3 : x^4 + 4 * x^2 ≥ 0 := by
          nlinarith [sq_nonneg (x^2), sq_nonneg (x)]
      linarith
    · -- Show x^4 + 4 * x^2 < 21
      nlinarith [sq_nonneg (x^2 - 3), sq_nonneg (x^2 + 4), sq_nonneg (x), sq_nonneg (x - 0)]