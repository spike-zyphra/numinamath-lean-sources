import Mathlib

theorem algebra_102156 :
    IsLeast {y : ℝ | ∃ x1 x2, y = (x1 + x2)^2 ∧ x1 * x2 = 2013} 8052 := by
  constructor
  · -- Show that 8052 is in the set
    use Real.sqrt 2013, Real.sqrt 2013
    constructor
    · -- Show $ (Real.sqrt 2013 + Real.sqrt 2013)^2 = 8052 $
      have h1 : (Real.sqrt 2013 : ℝ) ^ 2 = 2013 := Real.sq_sqrt (by norm_num)
      nlinarith [h1]
    · -- Show $ (Real.sqrt 2013) * (Real.sqrt 2013) = 2013 $
      have h1 : (Real.sqrt 2013 : ℝ) ^ 2 = 2013 := Real.sq_sqrt (by norm_num)
      nlinarith [h1]
  · -- Show that 8052 is indeed the minimum
    intro y hy
    rcases hy with ⟨x1, x2, h_eq, h_mul⟩
    nlinarith [sq_nonneg (x1 - x2), sq_nonneg (x1 + x2), sq_nonneg (x1 ^ 2 - x2 ^ 2), sq_nonneg (x1 * x2 - 2013)]