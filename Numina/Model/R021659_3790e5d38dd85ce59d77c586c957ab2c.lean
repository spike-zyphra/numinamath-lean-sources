import Mathlib

theorem algebra_781 : {x : ℝ | 4 * x ^ 2 + 12 * x * Real.sqrt (x + 1) = 27 * (x + 1)} = {3, 9 * (9 - √97) / 8} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · -- Assume the equation holds, prove x ∈ {3, 9 * (9 - √97) / 8}
    intro heq
    by_cases h1 : x + 1 ≥ 0
    · -- Let y = sqrt(x + 1)
      set y := Real.sqrt (x + 1) with hy
      have hy2 : y ^ 2 = x + 1 := Real.sq_sqrt h1
      have h2 : 4 * (y^2 - 1) ^ 2 + 12 * (y^2 - 1) * y = 27 * (y^2) := by
        have h3 : x = y ^ 2 - 1 := by
          nlinarith [hy2]
        rw [h3] at heq
        nlinarith
      have h3 : 4 * y ^ 4 + 12 * y ^ 3 - 35 * y ^ 2 - 12 * y + 4 = 0 := by
        nlinarith [h2]
      have h4 : (y + 1 / 2) * (y - 2) * (4 * y ^ 2 + 18 * y - 4) = 0 := by
        nlinarith [h3]
      cases' (mul_eq_zero.mp h4) with h5 h6
      cases' (mul_eq_zero.mp h5) with h7 h8
      · -- Case `y + 1/2 = 0`
        nlinarith [Real.sqrt_nonneg (x + 1)]
      · -- Case `y - 2 = 0`
        have h9 : y = 2 := by linarith
        have hx : x = 3 := by
          nlinarith [Real.sqrt_nonneg (x + 1), Real.sq_sqrt h1, h9]
        left; exact hx
      · -- Case `4 * y ^ 2 + 18 * y - 4 = 0`
        have h4y : 4 * y ^ 2 + 18 * y - 4 = 0 := h6
        have h9 : y = (-9 + Real.sqrt 97) / 4 := by
          have h10 : 4 * y ^ 2 + 18 * y - 4 = 0 := h4y
          have : (y - (-9 + Real.sqrt 97) / 4) * (y - (-9 - Real.sqrt 97) / 4) = 0 := by
            nlinarith [Real.sqrt_pos.2 (show 0 < (97 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (97 : ℝ) by norm_num), Real.sqrt_nonneg 97]
          cases' (mul_eq_zero.mp this) with h11 h12
          · -- `y - (-9 + Real.sqrt 97) / 4 = 0`
            linarith
          · -- `y - (-9 - Real.sqrt 97) / 4 = 0`
            nlinarith [Real.sqrt_pos.2 (show 0 < (97 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (97 : ℝ) by norm_num), Real.sqrt_nonneg 97, Real.sqrt_nonneg (x + 1)]
        have hx : x = 9 * (9 - Real.sqrt 97) / 8 := by
          nlinarith [Real.sqrt_nonneg (x + 1), Real.sq_sqrt h1, h9, Real.sqrt_nonneg 97, Real.sq_sqrt (show (0 : ℝ) ≤ (97 : ℝ) by norm_num)]
        right; exact hx
    · -- Assume x +1 < 0
      push_neg at h1
      have : x + 1 < 0 := by linarith
      have h11 : Real.sqrt (x + 1) = 0 := by
        rw [Real.sqrt_eq_zero'.mpr (by linarith)]
      rw [h11] at heq
      nlinarith
  · -- Show both sides satisfy the equation
    rintro (rfl | rfl)
    · -- Show 3 is a solution
      have h1 : Real.sqrt (3 + 1) = 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h1]
      nlinarith
    · -- Show 9 * (9 - Real.sqrt 97) / 8 is a solution
      have h1 : Real.sqrt (9 * (9 - Real.sqrt 97) / 8 + 1) = (-9 + Real.sqrt 97) / 4 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> nlinarith [Real.sqrt_pos.2 (show 0 < (97 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (97 : ℝ) by norm_num), Real.sqrt_nonneg 97]
      rw [h1]
      nlinarith [Real.sqrt_pos.2 (show 0 < (97 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (97 : ℝ) by norm_num), Real.sqrt_nonneg 97]