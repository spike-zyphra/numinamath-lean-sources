import Mathlib


theorem algebra_163115 :
    max (max (max (max (1 : ℝ) (Real.sqrt 29 - Real.sqrt 21)) (Real.pi / 3.142)) (5.1 * Real.sqrt 0.0361)) (6 / (Real.sqrt 13 + Real.sqrt 7)) = 1 := by


  have h1 : 1 ≥ Real.sqrt 29 - Real.sqrt 21 := by
    have h2 : Real.sqrt 21 + 1 ≥ Real.sqrt 29 := by
      have h3 : (Real.sqrt 21 + 1 : ℝ) ^ 2 ≥ (Real.sqrt 29 : ℝ) ^ 2 := by
        nlinarith [Real.sqrt_nonneg 21, Real.sqrt_nonneg 29,
          Real.sq_sqrt (show (0 : ℝ) ≤ (21 : ℝ) by norm_num),
          Real.sq_sqrt (show (0 : ℝ) ≤ (29 : ℝ) by norm_num),
          sq_nonneg (Real.sqrt 21 - Real.sqrt 29 + 1)]
      nlinarith [Real.sqrt_nonneg 21, Real.sqrt_nonneg 29, Real.sq_sqrt (show (0 : ℝ) ≤ (21 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (29 : ℝ) by norm_num)]
    linarith


  have h2 : 1 ≥ Real.pi / 3.142 := by
    have h3 : Real.pi < 3.1416 := by
      linarith [Real.pi_lt_31416]
    norm_num at h3 ⊢
    linarith


  have h3 : 1 ≥ 5.1 * Real.sqrt 0.0361 := by
    have h4 : Real.sqrt (0.0361 : ℝ) = (0.19 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h4]
    norm_num


  have h4 : 1 ≥ (6 / (Real.sqrt 13 + Real.sqrt 7) : ℝ) := by
    have h5 : Real.sqrt 13 + Real.sqrt 7 ≥ (6 : ℝ) := by
      nlinarith [Real.sqrt_nonneg 13, Real.sqrt_nonneg 7,
        Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num),
        Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num),
        sq_nonneg (Real.sqrt 13 - Real.sqrt 7),
        sq_nonneg (Real.sqrt 13 + Real.sqrt 7 - 6)]
    have h6 : (6 / (Real.sqrt 13 + Real.sqrt 7) : ℝ) ≤ (1 : ℝ) := by
      have h7 : Real.sqrt 13 + Real.sqrt 7 > 0 := by
        have h8 : Real.sqrt 13 > 0 := by
          apply Real.sqrt_pos.mpr
          all_goals norm_num
        have h9 : Real.sqrt 7 > 0 := by
          apply Real.sqrt_pos.mpr
          all_goals norm_num
        linarith
      apply (div_le_iff₀ (by linarith)).mpr
      nlinarith
    linarith


  have h5 : max (1 : ℝ) (Real.sqrt 29 - Real.sqrt 21) = 1 := by
    apply max_eq_left
    linarith [h1]
  have h6 : max (max (1 : ℝ) (Real.sqrt 29 - Real.sqrt 21)) (Real.pi / 3.142) = 1 := by
    rw [h5]
    apply max_eq_left
    linarith [h2]
  have h7 : max (max (max (1 : ℝ) (Real.sqrt 29 - Real.sqrt 21)) (Real.pi / 3.142)) (5.1 * Real.sqrt 0.0361) = 1 := by
    rw [h6]
    apply max_eq_left
    linarith [h3]
  have h8 : max (max (max (max (1 : ℝ) (Real.sqrt 29 - Real.sqrt 21)) (Real.pi / 3.142)) (5.1 * Real.sqrt 0.0361)) (6 / (Real.sqrt 13 + Real.sqrt 7)) = 1 := by
    rw [h7]
    apply max_eq_left
    linarith [h4]
  exact h8