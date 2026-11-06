import Mathlib

theorem algebra_22300 {x : ℝ} (hx : x ≠ -2 ∧ x ≠ 4 ∧ x ≠ -4 ∧ x ≠ 6 ∧ x ≠ -6 ∧ x ≠ 8) :
    ((x + 1) * (x - 3)) / (5 * (x + 2) * (x - 4)) +
    ((x + 3) * (x - 5)) / (9 * (x + 4) * (x - 6)) -
    2 * ((x + 5) * (x - 7)) / (13 * (x + 6) * (x - 8)) = 92 / 585 ↔
    x = 1 + Real.sqrt 19 ∨ x = 1 - Real.sqrt 19 := by
  rcases hx with ⟨hx1, hx2, hx3, hx4, hx5, hx6⟩
  constructor
  · -- Forward implication: if the equation holds, then x=1±√19
    intro h_eq
    have h1 : x + 2 ≠ 0 := by
      intro h2
      apply hx1
      linarith
    have h2 : x - 4 ≠ 0 := by
      intro h4
      apply hx2
      linarith
    have h3 : x + 4 ≠ 0 := by
      intro h4
      apply hx3
      linarith
    have h4 : x - 6 ≠ 0 := by
      intro h6
      apply hx4
      linarith
    have h5 : x + 6 ≠ 0 := by
      intro h6
      apply hx5
      linarith
    have h6 : x - 8 ≠ 0 := by
      intro h8
      apply hx6
      linarith
    field_simp [h1, h2, h3, h4, h5, h6] at h_eq 
    have h_eq_zero : (x - (1 + Real.sqrt 19)) * (x - (1 - Real.sqrt 19)) = 0 := by
      nlinarith [Real.sqrt_nonneg 19, Real.sq_sqrt (show 0 ≤ (19 : ℝ) by norm_num),
          sq_pos_of_pos (show Real.sqrt 19 > 0 by positivity),
          sq_pos_of_ne_zero (show (5 : ℝ) ≠ 0 by norm_num),
          sq_pos_of_ne_zero (show (9 : ℝ) ≠ 0 by norm_num),
          sq_pos_of_ne_zero (show (13 : ℝ) ≠ 0 by norm_num),
          sq_pos_of_ne_zero (show (x + 2) ≠ 0 by intro h2; apply hx1; linarith),
          sq_pos_of_ne_zero (show (x - 4) ≠ 0 by intro h2; apply hx2; linarith)
      ]
    cases' (mul_eq_zero.mp h_eq_zero) with h7 h8
    · -- First factor is zero
      left
      linarith 
    · -- Second factor is zero
      right
      linarith
  · -- Backward implication: if x=1±√19, then the equation holds
    rintro (h_eq | h_eq)
    · -- Case x = 1 + Real.sqrt 19
      rw [h_eq]
      have h1 : (1 + Real.sqrt 19 : ℝ) + 2 ≠ 0 := by nlinarith [Real.sqrt_pos.mpr (show 0 < (19 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (19 : ℝ) by norm_num)]
      have h2 : (1 + Real.sqrt 19 : ℝ) - 4 ≠ 0 := by nlinarith [Real.sqrt_pos.mpr (show 0 < (19 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (19 : ℝ) by norm_num)]
      have h3 : (1 + Real.sqrt 19 : ℝ) + 4 ≠ 0 := by nlinarith [Real.sqrt_pos.mpr (show 0 < (19 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (19 : ℝ) by norm_num)]
      have h4 : (1 + Real.sqrt 19 : ℝ) - 6 ≠ 0 := by nlinarith [Real.sqrt_pos.mpr (show 0 < (19 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (19 : ℝ) by norm_num)]
      have h5 : (1 + Real.sqrt 19 : ℝ) + 6 ≠ 0 := by nlinarith [Real.sqrt_pos.mpr (show 0 < (19 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (19 : ℝ) by norm_num)]
      have h6 : (1 + Real.sqrt 19 : ℝ) - 8 ≠ 0 := by nlinarith [Real.sqrt_pos.mpr (show 0 < (19 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (19 : ℝ) by norm_num)]
      field_simp [h1, h2, h3, h4, h5, h6]
      nlinarith [Real.sqrt_nonneg 19, Real.sq_sqrt (show 0 ≤ (19 : ℝ) by norm_num), sq_pos_of_pos (show Real.sqrt 19 > 0 by positivity)]
    · -- Case x = 1 - Real.sqrt 19
      rw [h_eq]
      have h1 : (1 - Real.sqrt 19 : ℝ) + 2 ≠ 0 := by nlinarith [Real.sqrt_pos.mpr (show 0 < (19 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (19 : ℝ) by norm_num)]
      have h2 : (1 - Real.sqrt 19 : ℝ) - 4 ≠ 0 := by nlinarith [Real.sqrt_pos.mpr (show 0 < (19 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (19 : ℝ) by norm_num)]
      have h3 : (1 - Real.sqrt 19 : ℝ) + 4 ≠ 0 := by nlinarith [Real.sqrt_pos.mpr (show 0 < (19 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (19 : ℝ) by norm_num)]
      have h4 : (1 - Real.sqrt 19 : ℝ) - 6 ≠ 0 := by nlinarith [Real.sqrt_pos.mpr (show 0 < (19 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (19 : ℝ) by norm_num)]
      have h5 : (1 - Real.sqrt 19 : ℝ) + 6 ≠ 0 := by nlinarith [Real.sqrt_pos.mpr (show 0 < (19 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (19 : ℝ) by norm_num)]
      have h6 : (1 - Real.sqrt 19 : ℝ) - 8 ≠ 0 := by nlinarith [Real.sqrt_pos.mpr (show 0 < (19 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (19 : ℝ) by norm_num)]
      field_simp [h1, h2, h3, h4, h5, h6]
      nlinarith [Real.sqrt_nonneg 19, Real.sq_sqrt (show 0 ≤ (19 : ℝ) by norm_num), sq_pos_of_pos (show Real.sqrt 19 > 0 by positivity)]