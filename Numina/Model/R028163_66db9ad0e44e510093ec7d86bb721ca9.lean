import Mathlib

theorem algebra_221262 (x : ℝ) (hx : x ^ 2 + 1 ≥ 0) :
    Real.logb 1997 (Real.sqrt (1 + x ^ 2) + x) =
    Real.logb 1996 (Real.sqrt (1 + x ^ 2) - x) ↔ x = 0 := by
  constructor
  · -- Assume the log equation holds, prove x = 0
    intro h
    have h2 : Real.sqrt (1 + x ^ 2) + x > 0 := by
      by_cases h3 : x ≥ 0
      · -- x ≥ 0
        nlinarith [Real.sqrt_nonneg (1 + x ^ 2), Real.sq_sqrt (show (0 : ℝ) ≤ (1 + x ^ 2 : ℝ) by nlinarith)]
      · -- x < 0
        have h4 : Real.sqrt (1 + x ^ 2) > -x := by
          nlinarith [Real.sqrt_nonneg (1 + x ^ 2), Real.sq_sqrt (show (0 : ℝ) ≤ (1 + x ^ 2 : ℝ) by nlinarith)]
        linarith
    have h3 : Real.sqrt (1 + x ^ 2) - x > 0 := by
      by_cases h4 : x ≥ 0
      · -- x ≥ 0
        have h4' : Real.sqrt (1 + x ^ 2) > x := by
          nlinarith [Real.sqrt_nonneg (1 + x ^ 2), Real.sq_sqrt (show (0 : ℝ) ≤ (1 + x ^ 2 : ℝ) by nlinarith)]
        linarith
      · -- x < 0
        nlinarith [Real.sqrt_nonneg (1 + x ^ 2), Real.sq_sqrt (show (0 : ℝ) ≤ (1 + x ^ 2 : ℝ) by nlinarith)]
    have h4 : Real.sqrt (1 + x ^ 2) - x = 1 / (Real.sqrt (1 + x ^ 2) + x) := by
      have h5 : (Real.sqrt (1 + x ^ 2) + x) * (Real.sqrt (1 + x ^ 2) - x) = 1 := by
        nlinarith [Real.sqrt_nonneg (1 + x ^ 2), Real.sq_sqrt (show (0 : ℝ) ≤ (1 + x ^ 2 : ℝ) by nlinarith)]
      have h6 : Real.sqrt (1 + x ^ 2) + x ≠ 0 := by
        linarith [show Real.sqrt (1 + x ^ 2) + x > (0 : ℝ) by linarith [h2]]
      field_simp [h6]
      nlinarith
    have h5 : Real.logb 1996 (Real.sqrt (1 + x ^ 2) - x) = - Real.logb 1996 (Real.sqrt (1 + x ^ 2) + x) := by
      rw [h4]
      simp [Real.logb_div, h2]
    have h6 : Real.logb 1997 (Real.sqrt (1 + x ^ 2) + x) + Real.logb 1996 (Real.sqrt (1 + x ^ 2) + x) = 0 := by
      linarith [h, h5]
    have pos1996 : (1996 : ℝ) > 1 := by norm_num
    have pos1997 : (1997 : ℝ) > 1 := by norm_num
    have h7 : Real.log (Real.sqrt (1 + x ^ 2) + x) = 0 := by 
      have eq : Real.log (Real.sqrt (1 + x ^ 2) + x) / Real.log (1997 : ℝ) + Real.log (Real.sqrt (1 + x ^ 2) + x) / Real.log (1996 : ℝ) = 0 := by
        have h7_1 : Real.logb 1997 (Real.sqrt (1 + x ^ 2) + x) = Real.log (Real.sqrt (1 + x ^ 2) + x) / Real.log 1997 := by
          field_simp [Real.logb]
        have h7_2 : Real.logb 1996 (Real.sqrt (1 + x ^ 2) + x) = Real.log (Real.sqrt (1 + x ^ 2) + x) / Real.log 1996 := by
          field_simp [Real.logb]
        linarith [h6, h7_1, h7_2]
      -- From `eq` we can deduce Real.log (X) = 0
      have h8 : Real.log (1997 : ℝ) > 0 := by
        apply Real.log_pos
        all_goals linarith
      have h9 : Real.log (1996 : ℝ) > 0 := by
        apply Real.log_pos
        all_goals linarith
      have eq2 : Real.log (Real.sqrt (1 + x ^ 2) + x) * (1/Real.log (1997 : ℝ) + 1/Real.log (1996 : ℝ)) = 0 := by
        have eq3 : Real.log (Real.sqrt (1 + x ^ 2) + x) / Real.log (1997 : ℝ) + Real.log (Real.sqrt (1 + x ^ 2) + x) / Real.log (1996 : ℝ) = 0 := eq
        field_simp [(show Real.log (1997 : ℝ) ≠ 0 by linarith)] at eq3 ⊢
        <;> nlinarith
      -- Real.log (√(1 + x ^ 2) + x) = 0
      have equation1 : Real.log (Real.sqrt (1 + x ^ 2) + x) = 0 := by
        have h14 : Real.log (1997 : ℝ) > 0 := h8
        have h15 : Real.log (1996 : ℝ) > 0 := h9
        have pos1 : Real.log (1997 : ℝ) ≠ 0 := by linarith
        have pos2 : Real.log (1996 : ℝ) ≠ 0 := by linarith
        have pos3 : (1 / Real.log (1997 : ℝ) + 1 / Real.log (1996 : ℝ)) ≠ 0 := by
          by_contra h
          have pos1997 : Real.log (1997 : ℝ) > 0 := by linarith
          have pos1996 : Real.log (1996 : ℝ) > 0 := by linarith
          have hpos : (1 / Real.log (1997 : ℝ) + 1 / Real.log (1996 : ℝ)) > 0 := by
            have h1 : 1 / Real.log (1997 : ℝ) > 0 := by
              apply div_pos
              norm_num
              linarith
            have h2 : 1 / Real.log (1996 : ℝ) > 0 := by
              apply div_pos
              norm_num
              linarith
            linarith
          nlinarith
        by_cases h14 : Real.log (Real.sqrt (1 + x ^ 2) + x) = 0
        · linarith
        · -- suppose `X` is non-zero
          have h15 : Real.log (Real.sqrt (1 + x ^ 2) + x) ≠ 0 := by
            intro h
            apply h14
            all_goals linarith
          have h16 : Real.log (Real.sqrt (1 + x ^ 2) + x) * (1/Real.log (1997 : ℝ) + 1/Real.log (1996 : ℝ)) ≠ 0 := by
            have h17 : Real.log (Real.sqrt (1 + x ^ 2) + x) ≠ 0 := h15
            have h18 : (1/Real.log (1997 : ℝ) + 1/Real.log (1996 : ℝ)) ≠ 0 := pos3
            exact mul_ne_zero h17 h18
          exfalso
          exact h16 eq2
      linarith [equation1]
    have h8 : Real.sqrt (1 + x ^ 2) + x = 1 := by
      have h77 : Real.log (Real.sqrt (1 + x ^ 2) + x) = 0 := h7
      have h11 : (Real.sqrt (1 + x ^ 2) + x : ℝ) > 0 := h2
      have h99 : (Real.sqrt (1 + x ^ 2) + x : ℝ) = 1 := by
        have h88 : Real.log (Real.sqrt (1 + x ^ 2) + x) = 0 := h77
        rw [Real.log_eq_zero] at h88
        rcases h88 with (r | r | r)
        · -- Case `r = 0`
          nlinarith
        · -- Case `r = 1`
          linarith
        · -- Case `r = -1`
          nlinarith
      linarith
    have h9 : x = 0 := by
      nlinarith [h8, Real.sqrt_nonneg (1 + x ^ 2), Real.sq_sqrt (show (0 : ℝ) ≤ (1 + x ^ 2 : ℝ) by nlinarith)
        ]
    tauto
  · -- Assume x = 0, prove the logarithm equality
    intro h
    rw [h]
    have h1 : Real.sqrt (1 + (0 : ℝ) ^ 2) = 1 := by
      norm_num [Real.sqrt_eq_iff_sq_eq]
    rw [h1]
    have h2 : Real.logb 1997 (1 + (0 : ℝ)) = 0 := by
      norm_num [Real.logb_one]
    have h3 : Real.logb 1996 (1 - (0 : ℝ)) = 0 := by
      norm_num [Real.logb_one]
    simp [h2, h3]