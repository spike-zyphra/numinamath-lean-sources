import Mathlib

theorem algebra_3803 :
  IsGreatest {z : ℝ | ∃ x y, z = 3 * x + y ∧ x ^ 2 + 2 * x * y + 4 * y ^ 2 ≤ 3} (Real.sqrt 31) := by

  constructor
  · -- First part: prove that sqrt 31 is in the set
    use 11 / Real.sqrt 31, -2 / Real.sqrt 31
    constructor
    · -- Check that 3x + y = sqrt 31
      have h1 : Real.sqrt 31 > 0 := by positivity
      have h2 : (Real.sqrt 31) ^ 2 = 31 := Real.sq_sqrt (by norm_num)
      field_simp [h1, h2]
      <;> nlinarith [Real.sqrt_nonneg 31, h2]
    · -- Check that x^2 + 2xy + 4y^2 ≤ 3
      have h1 : Real.sqrt 31 > 0 := by positivity
      have h2 : (Real.sqrt 31) ^ 2 = 31 := Real.sq_sqrt (by norm_num)
      field_simp [h1, h2]
      <;> nlinarith [Real.sqrt_nonneg 31, h2]

  · -- Second part: prove that sqrt 31 is the greatest
    intro z h
    rcases h with ⟨x, y, h1, h2⟩
    have h3 : (3 * x + y) ^ 2 ≤ 31 := by
      nlinarith [sq_nonneg (x + 11 * y), sq_nonneg (2 * x + 11 * y), sq_nonneg (x + 2 * y), sq_nonneg (x - 11 * y), sq_nonneg (x + 11 * y / 2), sq_nonneg (y + 2), sq_nonneg (x - 11), sq_nonneg (y + 2 / Real.sqrt 31), sq_nonneg (x - 11 / Real.sqrt 31)]
    have h4 : (3 * x + y) ≤ Real.sqrt 31 := by
      have h5 : Real.sqrt 31 ≥ 0 := by positivity
      have h6 : (Real.sqrt 31) ^ 2 = 31 := Real.sq_sqrt (by norm_num)
      nlinarith [Real.sqrt_nonneg 31, Real.sq_sqrt (show (0 : ℝ) ≤ 31 by norm_num), sq_nonneg ((3 * x + y) - Real.sqrt 31)]
    linarith [h1, h4]