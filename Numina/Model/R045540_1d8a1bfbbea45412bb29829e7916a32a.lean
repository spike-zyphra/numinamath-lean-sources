import Mathlib

open Real

theorem inequalities_316065 : √(6 + √(6 + √(6 + √(6 + √6)))) < 3 := by

  have h1 : √6 < 3 := by
    have h2 : √6 < √9 := by
      apply Real.sqrt_lt_sqrt
      all_goals norm_num
    have h3 : √9 = 3 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    linarith

  have h2 : √(6 + √6) < 3 := by
    have h3 : 6 + √6 < 9 := by
      nlinarith [h1, Real.sqrt_nonneg 6, Real.sq_sqrt (show 0 ≤ (6 : ℝ) by norm_num)]
    have h8 : √(6 + √6) < 3 := by
      have h9 : √6 ≥ 0 := Real.sqrt_nonneg 6
      have h10 : 6 + √6 ≥ 0 := by nlinarith
      have h11 : √(6 + √6) < 3 := by
        have h12 : (√(6 + √6)) ^ 2 < (3 : ℝ) ^ 2 := by
          have h13 : (√(6 + √6)) ^ 2 = 6 + √6 := by
            rw [Real.sq_sqrt]
            nlinarith [Real.sqrt_nonneg 6]
          rw [h13]
          nlinarith [h1, Real.sqrt_nonneg 6, Real.sq_sqrt (show 0 ≤ (6 : ℝ) by norm_num)]
        have h14 : (√(6 + √6)) ^ 2 < (3 : ℝ) ^ 2 := h12
        have h15 : √(6 + √6) ≥ 0 := Real.sqrt_nonneg (6 + √6)
        have h16 : (3 : ℝ) ≥ 0 := by norm_num
        nlinarith [sq_nonneg (√(6 + √6) - 3), Real.sq_sqrt (show 0 ≤ (6 + √6 : ℝ) by nlinarith [Real.sqrt_nonneg 6])]
      exact h11
    exact h8

  have h3 : √(6 + √(6 + √6)) < 3 := by
    have h4 : 6 + √(6 + √6) < 9 := by
      nlinarith [h2, Real.sqrt_nonneg (6 + √6), Real.sq_sqrt (show 0 ≤ (6 + √6 : ℝ) by positivity)]
    have h8 : √(6 + √(6 + √6)) < 3 := by
      have h9 : √(6 + √6) ≥ 0 := Real.sqrt_nonneg (6 + √6)
      have h10 : 6 + √(6 + √6) ≥ 0 := by nlinarith
      have h11 : √(6 + √(6 + √6)) < 3 := by
        have h12 : (√(6 + √(6 + √6))) ^ 2 < (3 : ℝ) ^ 2 := by
          have h13 : (√(6 + √(6 + √6))) ^ 2 = 6 + √(6 + √6) := by
            rw [Real.sq_sqrt]
            nlinarith [Real.sqrt_nonneg (6 + √6)]
          rw [h13]
          nlinarith [h2, Real.sqrt_nonneg (6 + √6), Real.sq_sqrt (show 0 ≤ (6 + √6 : ℝ) by positivity)]
        have h14 : (√(6 + √(6 + √6))) ^ 2 < (3 : ℝ) ^ 2 := h12
        have h15 : √(6 + √(6 + √6)) ≥ 0 := Real.sqrt_nonneg (6 + √(6 + √6))
        have h16 : (3 : ℝ) ≥ 0 := by norm_num
        nlinarith [sq_nonneg (√(6 + √(6 + √6)) - 3), Real.sq_sqrt (show 0 ≤ (6 + √(6 + √6) : ℝ) by positivity)]
      exact h11
    exact h8

  have h4 : √(6 + √(6 + √(6 + √6))) < 3 := by
    have h5 : 6 + √(6 + √(6 + √6)) < 9 := by
      nlinarith [h3, Real.sqrt_nonneg (6 + √(6 + √6)), Real.sq_sqrt (show 0 ≤ (6 + √(6 + √6) : ℝ) by positivity)]
    have h8 : √(6 + √(6 + √(6 + √6))) < 3 := by
      have h9 : √(6 + √(6 + √6)) ≥ 0 := Real.sqrt_nonneg (6 + √(6 + √6))
      have h10 : 6 + √(6 + √(6 + √6)) ≥ 0 := by nlinarith
      have h11 : √(6 + √(6 + √(6 + √6))) < 3 := by
        have h12 : (√(6 + √(6 + √(6 + √6)))) ^ 2 < (3 : ℝ) ^ 2 := by
          have h13 : (√(6 + √(6 + √(6 + √6)))) ^ 2 = 6 + √(6 + √(6 + √6)) := by
            rw [Real.sq_sqrt]
            nlinarith [Real.sqrt_nonneg (6 + √(6 + √6))]
          rw [h13]
          nlinarith [h3, Real.sqrt_nonneg (6 + √(6 + √6)), Real.sq_sqrt (show 0 ≤ (6 + √(6 + √6) : ℝ) by positivity)]
        have h14 : (√(6 + √(6 + √(6 + √6)))) ^ 2 < (3 : ℝ) ^ 2 := h12
        have h15 : √(6 + √(6 + √(6 + √6))) ≥ 0 := Real.sqrt_nonneg (6 + √(6 + √(6 + √6)))
        have h16 : (3 : ℝ) ≥ 0 := by norm_num
        nlinarith [sq_nonneg (√(6 + √(6 + √(6 + √6))) - 3), Real.sq_sqrt (show 0 ≤ (6 + √(6 + √(6 + √6)) : ℝ) by positivity)]
      exact h11
    exact h8

  have h5 : √(6 + √(6 + √(6 + √(6 + √6)))) < 3 := by
    have h6 : 6 + √(6 + √(6 + √(6 + √6))) < 9 := by
      nlinarith [h4, Real.sqrt_nonneg (6 + √(6 + √(6 + √6))), Real.sq_sqrt (show 0 ≤ (6 + √(6 + √(6 + √6)) : ℝ) by positivity)]
    have h8 : √(6 + √(6 + √(6 + √(6 + √6)))) < 3 := by
      have h9 : √(6 + √(6 + √(6 + √6))) ≥ 0 := Real.sqrt_nonneg (6 + √(6 + √(6 + √6)))
      have h10 : 6 + √(6 + √(6 + √(6 + √6))) ≥ 0 := by nlinarith
      have h11 : √(6 + √(6 + √(6 + √(6 + √6)))) < 3 := by
        have h12 : (√(6 + √(6 + √(6 + √(6 + √6))))) ^ 2 < (3 : ℝ) ^ 2 := by
          have h13 : (√(6 + √(6 + √(6 + √(6 + √6))))) ^ 2 = 6 + √(6 + √(6 + √(6 + √6))) := by
            rw [Real.sq_sqrt]
            nlinarith [Real.sqrt_nonneg (6 + √(6 + √(6 + √6)))]
          rw [h13]
          nlinarith [h4, Real.sqrt_nonneg (6 + √(6 + √(6 + √6))), Real.sq_sqrt (show 0 ≤ (6 + √(6 + √(6 + √6)) : ℝ) by positivity)]
        have h14 : (√(6 + √(6 + √(6 + √(6 + √6))))) ^ 2 < (3 : ℝ) ^ 2 := h12
        have h15 : √(6 + √(6 + √(6 + √(6 + √6)) )) ≥ 0 := Real.sqrt_nonneg (6 + √(6 + √(6 + √(6 + √6))))
        have h16 : (3 : ℝ) ≥ 0 := by norm_num
        nlinarith [sq_nonneg (√(6 + √(6 + √(6 + √(6 + √6)) )) - 3), Real.sq_sqrt (show 0 ≤ (6 + √(6 + √(6 + √(6 + √6)) )) by positivity)]
      exact h11
    exact h8

  exact h5