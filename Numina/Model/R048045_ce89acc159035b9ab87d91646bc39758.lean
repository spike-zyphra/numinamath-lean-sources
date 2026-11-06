import Mathlib

theorem algebra_105065 {a : ℝ} (ha : a = Real.sqrt (7 + Real.sqrt 13) - Real.sqrt (7 - Real.sqrt 13)) :
    ∃ n : ℕ, a^2 = n ∧ (a^3 - 2 * a - 1)^2016 = 1 := by
  have ha2 : a ^ 2 = 2 := by
    rw [ha]
    have h1 : Real.sqrt (7 + Real.sqrt 13) ^ 2 = 7 + Real.sqrt 13 := by
      rw [Real.sq_sqrt]
      positivity
    have h2 : Real.sqrt (7 - Real.sqrt 13) ^ 2 = 7 - Real.sqrt 13 := by
      rw [Real.sq_sqrt]
      have h5 : 7 - Real.sqrt 13 ≥ 0 := by
        have h6 : Real.sqrt 13 ≤ 7 := by
          nlinarith [Real.sqrt_nonneg 13, Real.sq_sqrt (show (0 : ℝ) ≤ 13 by norm_num), sq_nonneg (Real.sqrt 13 - 7)]
        linarith
      linarith
    have h3 : Real.sqrt (7 + Real.sqrt 13) * Real.sqrt (7 - Real.sqrt 13) = 6 := by
      have h4 : Real.sqrt (7 + Real.sqrt 13) * Real.sqrt (7 - Real.sqrt 13) = Real.sqrt ((7 + Real.sqrt 13) * (7 - Real.sqrt 13)) := by
        rw [← Real.sqrt_mul (by
          have h5 : 7 + Real.sqrt 13 ≥ 0 := by
            nlinarith [Real.sqrt_nonneg 13, Real.sq_sqrt (show (0 : ℝ) ≤ 13 by norm_num)]
          have h6 : 7 - Real.sqrt 13 ≥ 0 := by
            have h5 : 7 - Real.sqrt 13 ≥ 0 := by
              have h6 : Real.sqrt 13 ≤ 7 := by
                nlinarith [Real.sqrt_nonneg 13, Real.sq_sqrt (show (0 : ℝ) ≤ 13 by norm_num), sq_nonneg (Real.sqrt 13 - 7)]
              linarith
            nlinarith
          nlinarith
        )
        ]
        all_goals norm_num [Real.sqrt_nonneg, Real.sqrt_pos]
        all_goals nlinarith [Real.sqrt_nonneg 13, Real.sq_sqrt (show (0 : ℝ) ≤ 13 by norm_num)]
      rw [h4]
      have h5 : (7 + Real.sqrt 13) * (7 - Real.sqrt 13) = 36 := by
        nlinarith [Real.sqrt_nonneg 13, Real.sq_sqrt (show (0 : ℝ) ≤ 13 by norm_num)]
      rw [h5]
      have h6 : Real.sqrt ((36 : ℝ)) = 6 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h6]
    nlinarith [Real.sqrt_nonneg (7 + Real.sqrt 13), Real.sqrt_nonneg (7 - Real.sqrt 13), h1, h2, h3]
  use 2
  constructor
  · -- Show that a^2 = 2
    norm_num [ha2]
  · -- Calculate (a^3 - 2*a - 1)^2016 and prove that it equals 1
    have ha3 : a ^ 3 = 2 * a := by
      calc
        a ^ 3 = a * a ^ 2 := by ring
        _ = a * 2 := by rw [ha2]
        _ = 2 * a := by ring
    have h_eq : a^3 - 2 * a - 1 = -1 := by
      linarith [ha3]
    rw [h_eq]
    norm_num