import Mathlib

theorem algebra_20270 :
    IsLeast {d | ∃ x y : ℝ, d = Real.sqrt (x^2 + y^2) ∧ x^2 + 8 * x * y + 7 * y^2 = 225} 5 := by
  constructor
  · -- Show that 5 is in the set
    use Real.sqrt 5, 2 * Real.sqrt 5
    have h1 : (Real.sqrt 5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have h22 : (Real.sqrt 5 : ℝ) ^ 2 + (2 * Real.sqrt 5) ^ 2 = (25 : ℝ) := by
      nlinarith [h1, sq_nonneg (Real.sqrt 5)]
    have h23 : Real.sqrt ((Real.sqrt 5 : ℝ) ^ 2 + (2 * Real.sqrt 5) ^ 2) = 5 := by
      rw [h22]
      exact Real.sqrt_eq_cases.mpr (by norm_num)
    constructor
    · -- Show that 5 = sqrt(x^2 + y^2)
      linarith [h23]
    · -- Show that x^2 + 8 * x * y + 7 * y^2 = 225
      nlinarith [Real.sqrt_pos.mpr (show 0 < 5 by norm_num), Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]
  · -- Show that 5 is the least element in the set
    intro d hd
    rcases hd with ⟨x, y, h_eq, h_eq1⟩
    have h1 : x ^ 2 + y ^ 2 ≥ 25 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + 4 * y), sq_nonneg (y - 2 * x), sq_nonneg (y + 2 * x), sq_nonneg (x ^ 2 - 5), sq_nonneg ((2 * x - y) * (x - 2 * y)), sq_nonneg ((x + 2 * y) * (x - y)), sq_nonneg (x * y - (x * (x + y)))]
    have h2 : Real.sqrt (x^2 + y^2) ≥ (5 : ℝ) := by
      have h3 : Real.sqrt (x ^ 2 + y ^ 2) ≥ Real.sqrt (25 : ℝ) := Real.sqrt_le_sqrt (by linarith)
      have h4 : Real.sqrt (25 : ℝ) = 5 := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      linarith [h4, h3]
    linarith [h2, h_eq]