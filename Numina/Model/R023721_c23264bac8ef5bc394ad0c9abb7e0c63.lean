import Mathlib

theorem algebra_314679 :
    IsLeast {x | ∃ a b c d : ℝ, x = a^2 + b^2 + c^2 + d^2 + (a + b + c + d)^2 ∧ a + 2 * b + 3 * c + 4 * d = Real.sqrt 10} 1 := by 
  constructor
  · -- First part: show 1 is in the set
    use (-Real.sqrt 10 / 10), 0, (Real.sqrt 10 / 10), (Real.sqrt 10 / 5)
    constructor
    · -- Show the expression equals 1
      nlinarith [Real.sqrt_nonneg 10, Real.sq_sqrt (show 0 ≤ (10 : ℝ) by norm_num)]
    · -- Show the constraint is satisfied
      nlinarith [Real.sqrt_nonneg 10, Real.sq_sqrt (show 0 ≤ (10 : ℝ) by norm_num)]
  · -- Second part: show no value less than 1 is in the set
    intro x hx
    rcases hx with ⟨a, b, c, d, hx_eq, h⟩
    have h1 : a^2 + b^2 + c^2 + d^2 + (a + b + c + d)^2 ≥ 1 := by
      nlinarith [sq_nonneg (a + b + c + d - Real.sqrt 10 / 5), sq_nonneg (a + Real.sqrt 10 / 10), sq_nonneg (b), sq_nonneg (c - Real.sqrt 10 / 10), sq_nonneg (d - Real.sqrt 10 / 5), Real.sqrt_nonneg 10, Real.sq_sqrt (show 0 ≤ (10 : ℝ) by norm_num)]
    linarith [h1, hx_eq]