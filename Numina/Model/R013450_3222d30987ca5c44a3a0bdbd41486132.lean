import Mathlib

open Real

theorem inequalities_302120 {a b c : ℝ}
    (ha : a = sqrt 3 - sqrt 2) (hb : b = 2 - sqrt 3)
    (hc : c = sqrt (sqrt 5 - 2)) :
    c > a ∧ a > b := by

  have h1 : c > a := by
    rw [hc, ha]
    have h2 : sqrt (sqrt 5 - 2) ≥ 0 := by positivity
    have h3 : sqrt 3 - sqrt 2 ≥ 0 := by
      have h4 : sqrt 3 ≥ sqrt 2 := Real.sqrt_le_sqrt (by norm_num)
      linarith
    have h5 : (sqrt (sqrt 5 - 2)) ^ 2 > (sqrt 3 - sqrt 2) ^ 2 := by
      have h6 : (sqrt (sqrt 5 - 2)) ^ 2 = sqrt 5 - 2 := by
        rw [Real.sq_sqrt]
        have h7 : sqrt 5 ≥ 2 := by
          have h8 : sqrt 5 ≥ sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
          have h9 : sqrt 4 = 2 := Real.sqrt_eq_cases.mpr (by norm_num)
          linarith [h8, h9]
        linarith
        all_goals nlinarith [Real.sqrt_nonneg 5]

      have h7 : (sqrt 3 - sqrt 2) ^ 2 = 5 - 2 * (sqrt 6) := by
        have h10 : sqrt 6 = sqrt (3 * 2) := by norm_num
        have h11 : sqrt (3 * 2) = sqrt 3 * sqrt 2 := by
          rw [Real.sqrt_mul (by norm_num)]
          all_goals norm_num
        nlinarith [Real.sqrt_nonneg (3 * 2), Real.sq_sqrt (show 0 ≤ (3 * 2 : ℝ) by norm_num), 
          Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num),
          Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, 
          h10, h11, mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 2)]
      rw [h6, h7]
      nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sqrt_nonneg (6 : ℝ), Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (2 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (5 : ℝ)) (Real.sqrt_nonneg (6 : ℝ)),
        Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num),
        Real.sq_sqrt (show 0 ≤ (6 : ℝ) by norm_num),
        Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num),
        Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num),
        sq_nonneg (sqrt (5 : ℝ) - 2),
        sq_nonneg (sqrt (6 : ℝ) - 2),
        Real.sqrt_le_sqrt (show 4 ≤ (5 : ℝ) by norm_num),
        Real.sqrt_le_sqrt (show 4 ≤ (6 : ℝ) by norm_num),
        Real.sqrt_le_sqrt (show 25 ≤ (30 : ℝ) by norm_num),
        sq_nonneg (sqrt (5 : ℝ) + 2 * sqrt (6 : ℝ) - 7)]
    nlinarith [show sqrt (sqrt 5 - 2) ≥ 0 by positivity, show sqrt 3 - sqrt 2 ≥ 0 by
      have h4 : sqrt 3 ≥ sqrt 2 := Real.sqrt_le_sqrt (by norm_num)
      linarith, h5]

  have h2 : a > b := by
    rw [ha, hb]
    have h5 : sqrt 3 - sqrt 2 > 2 - sqrt 3 := by
      have h7 : sqrt 3 + sqrt 3 > 2 + sqrt 2 := by
        nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (2 : ℝ),
          Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), 
          Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num),
          sq_nonneg (sqrt (3 : ℝ) - 1), sq_nonneg (sqrt (2 : ℝ) - 1),
          Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (2 : ℝ),
          sq_nonneg (sqrt (3 : ℝ) ^ 2 - 3), sq_nonneg (sqrt (2 : ℝ) ^ 2 - 2)]
      nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (2 : ℝ)]
    linarith [h5]

  constructor
  · exact h1
  · exact h2