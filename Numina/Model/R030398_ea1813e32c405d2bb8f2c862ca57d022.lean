import Mathlib

theorem algebra_11514 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a * b * (a + b) = 4) :
    2 * a + b ≥ 2 * √3 ∧
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a * b * (a + b) = 4 ∧ 2 * a + b = 2 * √3 := by 
  have h1 : 2 * a + b ≥ 2 * √3 := by
    nlinarith [sq_nonneg ((2 * a + b) ^ 2 - 12), sq_nonneg (a - (√3 - 1)), sq_nonneg (b - 2), 
      sq_nonneg (a * b - (√3 - 1) * 2), sq_nonneg (a + b - (√3 - 1 + 2)), 
      mul_pos ha hb, 
      Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
  have h2 : ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a * b * (a + b) = 4 ∧ 2 * a + b = 2 * √3 := by
    use Real.sqrt 3 - 1, (2 : ℝ)
    constructor
    · -- Show a > 0 
      have h1 : 1 < Real.sqrt 3 := by
        rw [Real.lt_sqrt]
        all_goals norm_num
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    constructor
    · -- Show b > 0 
      norm_num
    constructor
    · -- Show a * b * (a + b) = 4 
      have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    · -- Show 2 * a + b = 2 * Real.sqrt 3 
      have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  constructor
  · exact h1 
  · exact h2