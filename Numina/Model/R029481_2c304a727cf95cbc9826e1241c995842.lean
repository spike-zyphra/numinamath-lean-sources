import Mathlib

theorem algebra_8544 {x : ℝ} (hx : 1 ≤ x) : x = Real.sqrt (x - 1 / x) + Real.sqrt (1 - 1 / x) ↔
    x = (1 + Real.sqrt 5) / 2 := by
  constructor
  · -- Assume x = √(x - 1/x) + √(1 - 1/x), prove x = (1 + √5)/2
    intro h_eq
    have h1 : 0 < x := by
      by_contra h
      push_neg at h
      have h2 : x ≤ 0 := by linarith
      linarith
    have h2' : x ≥ 1 := by linarith
    have h3 : Real.sqrt (x - 1 / x) ≥ 0 := by
      apply Real.sqrt_nonneg
    have h4 : Real.sqrt (1 - 1 / x) ≥ 0 := by
      apply Real.sqrt_nonneg
    have h5 : (Real.sqrt (x - 1 / x)) ^ 2 = x - 1 / x := by
      apply Real.sq_sqrt
      have h7 : x - 1 / x ≥ 0 := by
        have h8 : x ≥ 1 := by linarith
        have h9 : 1 / x ≤ 1 := by
          apply (div_le_one (by linarith)).mpr
          all_goals nlinarith
        nlinarith
      linarith
    have h6 : (Real.sqrt (1 - 1 / x)) ^ 2 = 1 - 1 / x := by
      apply Real.sq_sqrt
      have h7 : 1 - 1 / x ≥ 0 := by
        have h8 : x ≥ 1 := by linarith
        have h9 : 1 / x ≤ 1 := by
          apply (div_le_one (by linarith)).mpr
          all_goals nlinarith
        nlinarith
      linarith
    have eq5a : (x ^ 2 - x + 1) ^ 2 = (2 * x * Real.sqrt (1 - 1 / x)) ^ 2 := by
      have eq7 : x ^ 2 - x + 1 = 2 * x * Real.sqrt (1 - 1 / x) := by
        nlinarith [ h_eq, h5, h6, Real.sqrt_nonneg (x - 1 / x), Real.sqrt_nonneg (1 - 1 / x) ]
      rw [eq7]
    have eq5b : (2 * x * Real.sqrt (1 - 1 / x)) ^ 2 = 4 * x^2 * (1 - 1 / x) := by
      calc
        (2 * x * Real.sqrt (1 - 1 / x)) ^ 2 = 4 * x^2 * (Real.sqrt (1 - 1 / x) ^ 2) := by
          ring_nf
        _ = 4 * x^2 * (1 - 1 / x) := by
          rw [h6]
    have eq5c : (x ^ 2 - x + 1) ^ 2 = 4 * x^2 * (1 - 1 / x) := by
      rw [eq5a, eq5b]
    have eq6 : (x ^ 2 - x - 1) ^ 2 = 0 := by
      have eq7 : (x ^ 2 - x + 1) ^ 2 = 4 * x^2 * (1 - 1 / x) := eq5c
      field_simp [(show x ≠ 0 by linarith)] at eq7 ⊢
      nlinarith [ Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), sq_nonneg (x ^ 2 - x - 1) ]
    have eq8 : x^2 - x -1 =0 := by
      nlinarith 
    have eq9 : x = (1 + Real.sqrt 5) / 2 := by
      have h8 : x ^ 2 - x - 1 = 0 := eq8 
      have h9 : x ^ 2 - x - 1 = (x - (1 + Real.sqrt 5) / 2) * (x - (1 - Real.sqrt 5) / 2) := by
        nlinarith [ Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num) ]
      rw [h9] at h8 
      cases' (mul_eq_zero.1 h8) with h10 h11
      · -- Case x - (1 + Real.sqrt 5) / 2 = 0
        linarith 
      · -- Case x - (1 - Real.sqrt 5) / 2 = 0 
        -- Show this is a contradiction with x ≥ 1 
        have h12 : x = (1 - Real.sqrt 5) / 2 := by linarith 
        nlinarith [ Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num) ] 
    linarith
  · -- Assume x = (1 + √5)/2, prove x = √(x - 1/x) + √(1 - 1/x)
    rintro h_eq
    have h1 : 0 < x := by
      nlinarith [h_eq, Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num) ]
    have h2' : x ≥ 1 := by nlinarith [h_eq, Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num) ]
    have h9 : (1 / x) = (Real.sqrt 5 - 1) / 2 := by
      field_simp [show x ≠ 0 by linarith] at *
      nlinarith [ h_eq, Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num) ]
    have h9' : x - 1 / x = 1 := by
      nlinarith [ h_eq, Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num) ]
    have h11 : (1 - 1 / x) = (3 - Real.sqrt 5) / 2 := by
      nlinarith [ h_eq, Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num) ]
    have h9'' : Real.sqrt (x - 1 / x) = 1 := by
      rw [h9']
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h12 : Real.sqrt (1 - 1 / x) = (Real.sqrt 5 - 1) / 2 := by
      rw [h11]
      have hx : Real.sqrt ((3 - Real.sqrt 5) / 2) = (Real.sqrt 5 - 1) / 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> nlinarith [ Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), sq_nonneg (Real.sqrt 5 - 1 - 0) ]
      exact hx
    rw [h9'', h12]
    nlinarith [ h_eq, Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num) ]