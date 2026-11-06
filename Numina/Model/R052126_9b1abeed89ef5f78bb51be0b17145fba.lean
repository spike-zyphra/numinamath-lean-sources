import Mathlib

open Real

theorem algebra_195722 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : x + y = 18) :
    sqrt x + sqrt y ≤ 6 ∧
    ∃ x y : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ x + y = 18 ∧ sqrt x + sqrt y = 6 := by 
  have h1 : sqrt x + sqrt y ≤ 6 := by
    have h2 : (sqrt x) ^ 2 = x := Real.sq_sqrt hx
    have h3 : (sqrt y) ^ 2 = y := Real.sq_sqrt hy
    have h4 : sqrt x * sqrt y ≥ 0 := by nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y]
    nlinarith [sq_nonneg (sqrt x - sqrt y), sq_nonneg (sqrt x * sqrt y - 9), 
      Real.sqrt_nonneg x, Real.sqrt_nonneg y, 
      hxy, 
      sq_nonneg (x - 9), sq_nonneg (y - 9), 
      mul_nonneg (show 0 ≤ (x : ℝ) by linarith) (show 0 ≤ (y : ℝ) by linarith)
      ]
  have h2 : ∃ x y : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ x + y = 18 ∧ sqrt x + sqrt y = 6 := by
    use 9, 9 
    constructor
    · norm_num 
    constructor 
    · norm_num
    constructor 
    · norm_num 
    · 
      have h3 : sqrt (9 : ℝ) = 3 := by 
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      linarith [h3, Real.sqrt_nonneg (9 : ℝ), Real.sqrt_nonneg (9 : ℝ)]
  constructor 
  · exact h1 
  · exact h2