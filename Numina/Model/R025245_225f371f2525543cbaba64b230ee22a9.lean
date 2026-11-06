import Mathlib

theorem algebra_249254 (x : ℝ) (hx : x^2 - 2 * x + 3 ≠ 0 ∧ x^2 + 2 * x + 4 ≠ 0) :
    Real.sqrt ((x^2 - 2 * x + 3) / (x^2 + 2 * x + 4)) +
    Real.sqrt ((x^2 + 2 * x + 4) / (x^2 - 2 * x + 3)) = 5 / 2 ↔
    x = 2 ∨ x = 4 / 3 := by
  constructor
  · -- Assume left side is true, prove right side
    intro h
    have h1 : x^2 - 2 * x + 3 > 0 := by
      nlinarith [sq_nonneg (x - 1)]
    have h2 : x^2 + 2 * x + 4 > 0 := by
      nlinarith [sq_nonneg (x + 1)]
    have h3 : Real.sqrt ((x^2 - 2 * x + 3) / (x^2 + 2 * x + 4)) *
        Real.sqrt ((x^2 + 2 * x + 4) / (x^2 - 2 * x + 3)) = 1 := by
      have h4 : Real.sqrt ((x^2 - 2 * x + 3) / (x^2 + 2 * x + 4)) *
          Real.sqrt ((x^2 + 2 * x + 4) / (x^2 - 2 * x + 3)) =
          Real.sqrt (((x^2 - 2 * x + 3) / (x^2 + 2 * x + 4)) *
            ((x^2 + 2 * x + 4) / (x^2 - 2 * x + 3))) := by
        rw [← Real.sqrt_mul (by
          have h1' : (x^2 - 2 * x + 3) / (x^2 + 2 * x + 4) ≥ 0 := by
            apply div_nonneg
            linarith
            linarith
          have h2' : (x^2 + 2 * x + 4) / (x^2 - 2 * x + 3) ≥ 0 := by
            apply div_nonneg
            linarith
            linarith
          positivity
        )]
      rw [h4]
      have h5 : ((x^2 - 2 * x + 3) / (x^2 + 2 * x + 4)) *
          ((x^2 + 2 * x + 4) / (x^2 - 2 * x + 3)) = 1 := by
        field_simp [(show x^2 - 2 * x + 3 ≠ 0 by tauto), (show x^2 + 2 * x + 4 ≠ 0 by tauto)]
        <;> nlinarith
      rw [h5]
      simp
    have h4 : (Real.sqrt ((x^2 - 2 * x + 3) / (x^2 + 2 * x + 4)) - 2) * (Real.sqrt ((x^2 - 2 * x + 3) / (x^2 + 2 * x + 4)) - 1 / 2) = 0 := by
      nlinarith [h3, h, sq_nonneg (Real.sqrt ((x^2 - 2 * x + 3) / (x^2 + 2 * x + 4)) - 2), sq_nonneg (Real.sqrt ((x^2 + 2 * x + 4) / (x^2 - 2 * x + 3)) - 2)]
    cases' (mul_eq_zero.1 h4) with h5 h6
    · -- Case h1 = 2
      have h7 : Real.sqrt ((x^2 - 2 * x + 3) / (x^2 + 2 * x + 4)) = 2 := by linarith
      have h8 : (x^2 - 2 * x + 3) / (x^2 + 2 * x + 4) = 4 := by 
        have h9 : Real.sqrt ((x^2 - 2 * x + 3) / (x^2 + 2 * x + 4)) = 2 := h7
        have h10 : (Real.sqrt ((x^2 - 2 * x + 3) / (x^2 + 2 * x + 4))) ^ 2 = 4 := by 
          rw [h9]
          norm_num
        have h11 : (Real.sqrt ((x^2 - 2 * x + 3) / (x^2 + 2 * x + 4))) ^ 2 = (x^2 - 2 * x + 3) / (x^2 + 2 * x + 4) := by
          rw [Real.sq_sqrt]
          have h14 : (x^2 - 2 * x + 3) / (x^2 + 2 * x + 4) ≥ 0 := by
            apply div_nonneg
            linarith
            linarith
          linarith
        linarith [h10, h11]
      have h9 : x^2 - 2 * x + 3 = 4 * (x^2 + 2 * x + 4) := by
        field_simp [(show x^2 + 2 * x + 4 ≠ 0 by tauto)] at h8
        nlinarith
      have h2' : 3 * x^2 + 10 * x + 13 = 0 := by 
        nlinarith 
      nlinarith [sq_nonneg (x + 5 / 3)]
    · -- Case h6 = 1/2 
      have h7 : Real.sqrt ((x^2 - 2 * x + 3) / (x^2 + 2 * x + 4)) = 1 / 2 := by linarith 
      -- Real.sqrt a = 1/2 => a = 1/4 
      have h8 : (x^2 - 2 * x + 3) / (x^2 + 2 * x + 4) = 1 / 4 := by 
        have h9 : Real.sqrt ((x^2 - 2 * x + 3) / (x^2 + 2 * x + 4)) = 1 / 2 := h7 
        have h10 : (Real.sqrt ((x^2 - 2 * x + 3) / (x^2 + 2 * x + 4))) ^ 2 = 1 / 4 := by 
          rw [h9] 
          norm_num 
        have h11 : (Real.sqrt ((x^2 - 2 * x + 3) / (x^2 + 2 * x + 4))) ^ 2 = (x^2 - 2 * x + 3) / (x^2 + 2 * x + 4) := by 
          rw [Real.sq_sqrt] 
          have h14 : (x^2 - 2 * x + 3) / (x^2 + 2 * x + 4) ≥ 0 := by 
            apply div_nonneg 
            linarith 
            linarith 
          linarith 
        linarith [h10, h11] 
      have h9 : 4 * (x^2 - 2 * x + 3) = x^2 + 2 * x + 4 := by 
        have h10 : (x^2 - 2 * x + 3) / (x^2 + 2 * x + 4) = 1 / 4 := h8 
        have h2ne : x^2 + 2 * x + 4 ≠ 0 := by tauto 
        field_simp [h2ne] at h10 ⊢ 
        nlinarith 
      have h2' : 3 * x^2 - 10 * x + 8 = 0 := by 
        nlinarith 
      have h5 : (x - 2) * (3 * x - 4) = 0 := by 
        nlinarith [h2'] 
      cases' (mul_eq_zero.1 h5) with h6 h7 
      · -- Case h6 : x = 2 
        left 
        linarith 
      · -- Case h7 : 3 * x - 4 = 0 
        right 
        linarith 
  · -- Assume right side is true, prove left side 
    rintro (h | h)
    · -- Case h : x = 2 
      rw [h] 
      have h1 : Real.sqrt (( (2 : ℝ) ^2 - 2 * (2 : ℝ) + 3 ) / ( (2 : ℝ) ^2 + 2 * (2 : ℝ) + 4 )) = 1 / 2 := by 
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
      have h2 : Real.sqrt (( (2 : ℝ) ^2 + 2 * (2 : ℝ) + 4 ) / ( (2 : ℝ) ^2 - 2 * (2 : ℝ) + 3 )) = 2 := by 
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
      rw [h1, h2] 
      all_goals norm_num 
    · -- Case h : x = 4 / 3 
      rw [h] 
      have h1 : Real.sqrt (( (4 / 3 : ℝ) ^2 - 2 * (4 / 3 : ℝ) + 3 ) / ( (4 / 3 : ℝ) ^2 + 2 * (4 / 3 : ℝ) + 4 )) = 1 / 2 := by 
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
      have h2 : Real.sqrt (( (4 / 3 : ℝ) ^2 + 2 * (4 / 3 : ℝ) + 4 ) / ( (4 / 3 : ℝ) ^2 - 2 * (4 / 3 : ℝ) + 3 )) = 2 := by 
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
      rw [h1, h2] 
      all_goals norm_num