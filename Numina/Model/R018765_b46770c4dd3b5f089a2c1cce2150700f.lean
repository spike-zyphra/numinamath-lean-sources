import Mathlib

open Real Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem inequalities_307963 (x y : ℝ) (z : ℂ) (hz : z = x + y * .I) :
    (|x| + |y|) / Real.sqrt 2 ≤ abs z ∧ abs z ≤ |x| + |y| := by
  have h1 : abs z = Real.sqrt (x^2 + y^2) := by
    rw [hz]
    simp [Complex.abs, Complex.normSq]
    <;> ring_nf
    <;> norm_num
    <;> ring_nf
  rw [h1]
  constructor
  · -- First goal: (|x| + |y|) / sqrt 2 ≤ sqrt (x^2 + y^2)
    have h4 : (|x| + |y|) / Real.sqrt 2 ≤ Real.sqrt (x^2 + y^2) := by
      have h4 : ( (|x| + |y| : ℝ) / Real.sqrt 2 ) ^ 2 ≤ (x^2 + y^2) := by
        have h5 : (|x| + |y|) ^ 2 / (2 : ℝ) ≤ (x^2 + y^2) := by
          have h6 : (|x| + |y|) ^ 2 ≤ 2 * (x^2 + y^2) := by
            have h7 : |x| ^ 2 = x^2 := by
              cases' abs_cases x with hx hx
              · nlinarith
              · nlinarith
            have h8 : |y| ^ 2 = y^2 := by
              cases' abs_cases y with hy hy
              · nlinarith
              · nlinarith
            have h9 : (|x| + |y|) ^ 2 = |x| ^ 2 + 2 * |x| * |y| + |y| ^ 2 := by
              ring
            nlinarith [sq_nonneg (|x| - |y|), h7, h8]
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]
        have h6 : ( (|x| + |y| : ℝ) / Real.sqrt 2 ) ^ 2 = (|x| + |y|) ^ 2 / (2 : ℝ) := by
          field_simp [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
          <;> ring_nf <;> norm_num
        nlinarith
      -- Now convert the squared inequality to the original one
      have h5 : ( (|x| + |y| : ℝ) / Real.sqrt 2 ) ≤ Real.sqrt (x^2 + y^2) := by
        have h6 : ( (|x| + |y| : ℝ) / Real.sqrt 2 ) ^ 2 ≤ (Real.sqrt (x^2 + y^2) : ℝ) ^ 2 := by
          nlinarith [Real.sqrt_nonneg (x^2 + y^2), Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (x^2 + y^2) by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
        nlinarith [Real.sqrt_nonneg (x^2 + y^2), Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (x^2 + y^2) by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg ( (|x| + |y|) / Real.sqrt 2 ) ]
      linarith
    exact h4
  · -- Second goal: sqrt (x^2 + y^2) ≤ |x| + |y|
    have h6 : Real.sqrt (x^2 + y^2) ≤ (|x| + |y| : ℝ) := by
      -- We will square both sides to remove the square root
      have h7 : (Real.sqrt (x^2 + y^2)) ^ 2 ≤ (|x| + |y| : ℝ) ^ 2 := by
        -- LHS is x^2+y^2
        have h8 : (Real.sqrt (x^2 + y^2)) ^ 2 = x^2 + y^2 := by
          rw [Real.sq_sqrt]
          nlinarith [sq_nonneg x, sq_nonneg y]
        -- RHS is |x|^2 + 2|x||y| + |y|^2 = x^2 + 2|x||y| + y^2
        have h9 : (|x| + |y| : ℝ) ^ 2 = |x| ^ 2 + 2 * |x| * |y| + |y| ^ 2 := by
          ring
        rw [h8, h9]
        -- Inequality becomes x^2+y^2 <= x^2+2|x||y|+y^2
        -- This is equivalent to 0 <= 2|x||y|
        have hx : |x| ^ 2 = x^2 := by cases' abs_cases x with hx hx <;> nlinarith
        have hy : |y| ^ 2 = y^2 := by cases' abs_cases y with hy hy <;> nlinarith
        have habs_nonneg : |x| ≥ 0 := abs_nonneg x
        have habs_nonneg' : |y| ≥ 0 := abs_nonneg y
        nlinarith [abs_nonneg x, abs_nonneg y]
      have h8 : (Real.sqrt (x^2 + y^2) : ℝ) ≤ (|x| + |y| : ℝ) := by
        nlinarith [Real.sqrt_nonneg (x^2 + y^2), abs_nonneg (x), abs_nonneg (y), Real.sq_sqrt (show (0 : ℝ) ≤ (x^2 + y^2 : ℝ) by positivity)]
      linarith
    exact h6