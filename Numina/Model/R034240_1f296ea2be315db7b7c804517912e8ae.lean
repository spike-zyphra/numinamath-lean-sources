import Mathlib

theorem algebra_222956 :
    {(x, y) : ℝ × ℝ | 0 ≤ 7 * x + y ∧ 0 ≤ x + y ∧ Real.sqrt (7 * x + y) + Real.sqrt (x + y) = 6 ∧ Real.sqrt (x + y) - y + x = 2} = {(2, 2)} := by
  ext ⟨x, y⟩
  simp
  constructor
  · -- Assume (x, y) is in the left side; prove (x, y) = (2, 2)
    rintro ⟨h1, h2, h3, h4⟩
    have h5 : Real.sqrt (x + y) = 2 + y - x := by linarith
    have h8 : Real.sqrt (7 * x + y) = 4 + x - y := by 
      nlinarith [h3, h5]
    have h6 : (Real.sqrt (x + y)) ^ 2 = x + y := Real.sq_sqrt (by linarith)
    have h7 : (Real.sqrt (7 * x + y)) ^ 2 = 7 * x + y := Real.sq_sqrt (by linarith)
    rw [h5] at h6
    rw [h8] at h7
    have h9 : (2 + y - x) ^ 2 = x + y := by nlinarith
    have h10 : (4 + x - y) ^ 2 = 7 * x + y := by nlinarith
    have h11 : x = 2 * y - 2 := by
      nlinarith
    rw [h11] at h10
    have h12 : y ^ 2 - 11 * y + 18 = 0 := by 
      nlinarith
    have h13 : (y - 9) * (y - 2) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h13) with h14 h15
    · -- Case where y = 9 
      have h16 : y = 9 := by linarith
      have h17 : x = 16 := by
        nlinarith [h16, h11]
      nlinarith [Real.sqrt_nonneg (7 * x + y), Real.sqrt_nonneg (x + y), 
              h3, h4, Real.sq_sqrt (show 0 ≤ (7 * x + y : ℝ) by nlinarith), 
              Real.sq_sqrt (show 0 ≤ (x + y : ℝ) by nlinarith)]
    · -- Case where y = 2
      have h18 : y = 2 := by linarith
      have h19 : x = 2 := by
        nlinarith [h18, h11]
      simp [h19, h18]
  · -- Assume (x, y) = (2, 2)
    rintro ⟨rfl, rfl⟩
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · -- Show sqrt(16) + sqrt(4) = 4 + 2 = 6
      have h1 : Real.sqrt (7 * (2 : ℝ) + (2 : ℝ)) = 4 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h2 : Real.sqrt ((2 : ℝ) + (2 : ℝ)) = 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      linarith [h1, h2]
    · -- Show sqrt(4) - 2 + 2 = 2 - 2 + 2 = 2
      have h3 : Real.sqrt ((2 : ℝ) + (2 : ℝ)) = 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      linarith [h3]