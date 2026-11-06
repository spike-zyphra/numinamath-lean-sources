import Mathlib

theorem algebra_192530 : (9 + √80) ^ ((1 : ℝ) / 3) + (9 - √80) ^ ((1 : ℝ) / 3) = 3 := by
  have h1 : ((9 + Real.sqrt 80) ^ ((1 : ℝ) / 3)) ^ 3 = 9 + Real.sqrt 80 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_num
    all_goals
      have h2 : 9 + Real.sqrt 80 ≥ 0 := by
        have h3 : Real.sqrt 80 ≥ 0 := Real.sqrt_nonneg 80
        linarith [Real.sqrt_nonneg 80]
      positivity

  have h2 : ((9 - Real.sqrt 80) ^ ((1 : ℝ) / 3)) ^ 3 = 9 - Real.sqrt 80 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_num
    all_goals
      have h3 : 9 - Real.sqrt 80 ≥ 0 := by
        nlinarith [Real.sqrt_nonneg 80, Real.sq_sqrt (show (0 : ℝ) ≤ 80 by norm_num), Real.sqrt_le_sqrt (show (0 : ℝ) ≤ 80 by norm_num)]
      positivity

  have h3 : (9 + Real.sqrt 80) * (9 - Real.sqrt 80) = 1 := by
    nlinarith [Real.sqrt_nonneg 80, Real.sq_sqrt (show (0 : ℝ) ≤ 80 by norm_num)]

  have h4 : ((9 + Real.sqrt 80) ^ ((1 : ℝ) / 3)) * ((9 - Real.sqrt 80) ^ ((1 : ℝ) / 3)) = (1 : ℝ) := by
    have h5 : ((9 + Real.sqrt 80) ^ ((1 : ℝ) / 3)) * ((9 - Real.sqrt 80) ^ ((1 : ℝ) / 3)) = ((9 + Real.sqrt 80) * (9 - Real.sqrt 80)) ^ ((1 : ℝ) / 3) := by
      rw [← Real.mul_rpow]
      all_goals
        have h2 : 9 + Real.sqrt 80 ≥ 0 := by
          have h3 : Real.sqrt 80 ≥ 0 := Real.sqrt_nonneg 80
          linarith [Real.sqrt_nonneg 80]
        have h3 : 9 - Real.sqrt 80 ≥ 0 := by
          nlinarith [Real.sqrt_nonneg 80, Real.sq_sqrt (show (0 : ℝ) ≤ 80 by norm_num), Real.sqrt_le_sqrt (show (0 : ℝ) ≤ 80 by norm_num)]
        all_goals linarith

    rw [h5, h3]
    have h6 : (1 : ℝ) ^ ((1 : ℝ) / 3) = 1 := by
      have h7 : (1 : ℝ) ^ ((1 : ℝ) / 3) = 1 := by
        rw [Real.one_rpow]
      linarith
    linarith

  have h11 : ((9 + Real.sqrt 80) ^ ((1 : ℝ) / 3) + (9 - Real.sqrt 80) ^ ((1 : ℝ) / 3)) ^ 3 = 18 + 3 * ((9 + Real.sqrt 80) ^ ((1 : ℝ) / 3) + (9 - Real.sqrt 80) ^ ((1 : ℝ) / 3)) := by
    have h10 : ((9 + Real.sqrt 80) ^ ((1 : ℝ) / 3) + (9 - Real.sqrt 80) ^ ((1 : ℝ) / 3)) ^ 3 =
        ((9 + Real.sqrt 80) ^ ((1 : ℝ) / 3)) ^ 3 + ((9 - Real.sqrt 80) ^ ((1 : ℝ) / 3)) ^ 3 + 3 * ((9 + Real.sqrt 80) ^ ((1 : ℝ) / 3) * ((9 - Real.sqrt 80) ^ ((1 : ℝ) / 3)) ) * ((9 + Real.sqrt 80) ^ ((1 : ℝ) / 3) + (9 - Real.sqrt 80) ^ ((1 : ℝ) / 3)) := by
      ring
    rw [h10, h1, h2, h4]
    all_goals nlinarith [Real.sqrt_nonneg 80, Real.sq_sqrt (show (0 : ℝ) ≤ 80 by norm_num)]

  have h12 : ((9 + Real.sqrt 80) ^ ((1 : ℝ) / 3) + (9 - Real.sqrt 80) ^ ((1 : ℝ) / 3) - 3) * (((9 + Real.sqrt 80) ^ ((1 : ℝ) / 3) + (9 - Real.sqrt 80) ^ ((1 : ℝ) / 3)) ^ 2 + 3 * ((9 + Real.sqrt 80) ^ ((1 : ℝ) / 3) + (9 - Real.sqrt 80) ^ ((1 : ℝ) / 3)) + 6) = 0 := by
    nlinarith [sq_nonneg (((9 + Real.sqrt 80) ^ ((1 : ℝ) / 3) + (9 - Real.sqrt 80) ^ ((1 : ℝ) / 3)) ^ 2 - 9), sq_nonneg (((9 + Real.sqrt 80) ^ ((1 : ℝ) / 3)) - (9 - Real.sqrt 80) ^ ((1 : ℝ) / 3)), sq_nonneg ((9 + Real.sqrt 80) ^ ((1 : ℝ) / 3)), sq_nonneg ((9 - Real.sqrt 80) ^ ((1 : ℝ) / 3)), Real.sqrt_nonneg 80]

  cases (mul_eq_zero.mp h12) with
  | inl h13 =>
    nlinarith
  | inr h13 =>
    have h14 : ((9 + Real.sqrt 80) ^ ((1 : ℝ) / 3) + (9 - Real.sqrt 80) ^ ((1 : ℝ) / 3)) ^ 2 + 3 * ((9 + Real.sqrt 80) ^ ((1 : ℝ) / 3) + (9 - Real.sqrt 80) ^ ((1 : ℝ) / 3)) + 6 > 0 := by
      have h15 : ((9 + Real.sqrt 80) ^ ((1 : ℝ) / 3)) ≥ 0 := by
        apply Real.rpow_nonneg
        have h15 : 9 + Real.sqrt 80 ≥ 0 := by
          have h3 : Real.sqrt 80 ≥ 0 := Real.sqrt_nonneg 80
          linarith [Real.sqrt_nonneg 80]
        linarith

      have h16 : (9 - Real.sqrt 80) ^ ((1 : ℝ) / 3) ≥ 0 := by
        apply Real.rpow_nonneg
        have h17 : 9 - Real.sqrt 80 ≥ 0 := by
          nlinarith [Real.sqrt_nonneg 80, Real.sq_sqrt (show (0 : ℝ) ≤ 80 by norm_num), Real.sqrt_le_sqrt (show (0 : ℝ) ≤ 80 by norm_num)]
        linarith

      nlinarith [sq_nonneg (((9 + Real.sqrt 80) ^ ((1 : ℝ) / 3) + (9 - Real.sqrt 80) ^ ((1 : ℝ) / 3)) ), sq_nonneg (((9 + Real.sqrt 80) ^ ((1 : ℝ) / 3)) - (9 - Real.sqrt 80) ^ ((1 : ℝ) / 3)), sq_nonneg (((9 + Real.sqrt 80) ^ ((1 : ℝ) / 3)) ), sq_nonneg (((9 - Real.sqrt 80) ^ ((1 : ℝ) / 3)) ), Real.sqrt_nonneg 80, Real.sq_sqrt (show (0 : ℝ) ≤ 80 by norm_num)]
    linarith