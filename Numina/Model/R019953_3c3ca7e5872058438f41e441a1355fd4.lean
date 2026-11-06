import Mathlib

theorem algebra_225022 (a b : ℝ) (ha : a ≠ 0) :
    1 / a^2 + 2 * a^2 + 3 * b^2 + 4 * a * b ≥ Real.sqrt (8 / 3) := by
  have h1 : 1 / a^2 + 2 * a^2 + 3 * b^2 + 4 * a * b - Real.sqrt (8 / 3) ≥ 0 := by
    have h2 : 3 * b^2 + 4 * a * b = 3 * (b + 2 * a / 3)^2 - 4 * a^2 / 3 := by
      ring_nf
    have h3 : 1 / a^2 + 2 * a^2 + 3 * b^2 + 4 * a * b = 1 / a^2 + 2 * a^2 / 3 + 3 * (b + 2 * a / 3)^2 := by
      nlinarith [h2, sq_nonneg (a), sq_nonneg (b + 2 * a / 3)]
    rw [h3]
    have h4 : 3 * (b + 2 * a / 3)^2 ≥ 0 := by
      apply mul_nonneg
      norm_num
      apply pow_two_nonneg
    have h5 : 1 / a^2 + 2 * a^2 / 3 ≥ Real.sqrt (8 / 3) := by
      have h6 : 1 / a^2 + 2 * a^2 / 3 - Real.sqrt (8 / 3) ≥ 0 := by
        have h8 : 1 / a^2 + 2 * a^2 / 3 ≥ 2 * Real.sqrt (2 / 3) := by
          have h9 : 0 < (a^2 : ℝ) := by
            exact sq_pos_of_ne_zero ha
          have h10 : (1 / a^2 : ℝ) ≥ 0 := by positivity
          have h11 : (2 * a^2 / 3 : ℝ) ≥ 0 := by positivity
          have h12 : Real.sqrt ((1 / a^2 : ℝ) * (2 * a^2 / 3 : ℝ)) = Real.sqrt (2 / 3 : ℝ) := by
            have h13 : (1 / a^2 : ℝ) * (2 * a^2 / 3 : ℝ) = (2 / 3 : ℝ) := by
              field_simp
              <;> ring_nf
              <;> nlinarith [sq_nonneg (a)]
            rw [h13]
          have h14 : (Real.sqrt ((1 / a^2 : ℝ) ) - Real.sqrt ((2 * a^2 / 3 : ℝ)) )^2 ≥ 0 := by
            positivity
          have h15 : (Real.sqrt ((1 / a^2 : ℝ) ) - Real.sqrt ((2 * a^2 / 3 : ℝ)) )^2 = (1 / a^2 : ℝ) + (2 * a^2 / 3 : ℝ) - 2 * Real.sqrt (((1 / a^2 : ℝ) ) * (2 * a^2 / 3 : ℝ) ) := by
            have h16 : Real.sqrt ((1 / a^2 : ℝ) )^2 = (1 / a^2 : ℝ) := by
              rw [Real.sq_sqrt]
              positivity
            have h17 : Real.sqrt ((2 * a^2 / 3 : ℝ) )^2 = (2 * a^2 / 3 : ℝ) := by
              rw [Real.sq_sqrt]
              positivity
            have h18 : Real.sqrt ((1 / a^2 : ℝ) ) * Real.sqrt ((2 * a^2 / 3 : ℝ) ) = Real.sqrt (((1 / a^2 : ℝ) ) * (2 * a^2 / 3 : ℝ) ) := by
              rw [Real.sqrt_mul (by positivity)]
            nlinarith [Real.sqrt_nonneg ((1 / a^2 : ℝ) ), Real.sqrt_nonneg ((2 * a^2 / 3 : ℝ) ), h16, h17, h18]
          nlinarith [Real.sqrt_nonneg ((1 / a^2 : ℝ) ), Real.sqrt_nonneg ((2 * a^2 / 3 : ℝ) ), Real.sq_sqrt (show (0 : ℝ) ≤ (1 / a^2 : ℝ)  by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ (2 * a^2 / 3 : ℝ)  by positivity), h12]
        have h17 : 2 * Real.sqrt (2 / 3 : ℝ) = Real.sqrt (8 / 3 : ℝ) := by
          have h18 : Real.sqrt (8 / 3 : ℝ) = Real.sqrt (4 * (2 / 3 : ℝ) ) := by
            ring_nf
          rw [h18]
          have h19 : Real.sqrt (4 * (2 / 3 : ℝ) ) = Real.sqrt (4 : ℝ) * Real.sqrt (2 / 3 : ℝ) := by
            rw [Real.sqrt_mul (by positivity)]
          rw [h19]
          have h20 : Real.sqrt (4 : ℝ) = 2 := by
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          rw [h20]
          all_goals norm_num
        nlinarith [h8, h17]
      nlinarith [Real.sqrt_nonneg (8 / 3 : ℝ)]
    linarith [h4, h5]
  linarith