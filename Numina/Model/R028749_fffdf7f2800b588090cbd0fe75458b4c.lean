import Mathlib

open Real Set

theorem algebra_251729 (x : ℝ) :
    2 * abs (x ^ 2 + 2 * x - 5) = x - 1 ∧ x < sqrt 2 ↔
    x = (sqrt 113 - 5) / 4 := by
  constructor
  · -- Assume (2 * abs (x ^ 2 + 2 * x - 5) = x - 1 ∧ x < sqrt 2), prove x = (sqrt 113 - 5) / 4
    intro h
    rcases h with ⟨h_eq, h_lt⟩
    by_cases h1 : x ^ 2 + 2 * x - 5 ≥ 0
    · -- Case x^2 + 2 * x - 5 ≥ 0
      have h2 : abs (x ^ 2 + 2 * x - 5) = x ^ 2 + 2 * x - 5 := by
        rw [abs_of_nonneg h1]
      rw [h2] at h_eq
      have h2_eq : 2 * (x ^ 2) + 3 * x - 9 = 0 := by nlinarith
      have h3 : (x - 3 / 2) * (x + 3) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 h3) with h4 h5
      · -- x = 3/2
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      · -- x = -3
        nlinarith [abs_nonneg (x ^ 2 + 2 * x - 5), abs_nonneg (x ^ 2 + 2 * x - 5), h_eq, h1]
    · -- Case x^2 + 2 * x - 5 < 0
      have h2 : abs (x ^ 2 + 2 * x - 5) = -(x ^ 2 + 2 * x - 5) := by
        rw [abs_of_neg (by linarith)]
      rw [h2] at h_eq
      have h2_eq : 2 * (x ^ 2) + 5 * x - 11 = 0 := by
        nlinarith
      have h3 : (x - (sqrt 113 - 5) / 4) * (x - (-5 - sqrt 113) / 4) = 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (113 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (113 : ℝ) by norm_num)]
      cases' (mul_eq_zero.1 h3) with h4 h5
      · -- First root
        linarith
      · -- Second root
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (113 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (113 : ℝ) by norm_num)]
  · -- Backward direction
    intro h_eq
    constructor
    · -- Show that 2 * abs (x ^ 2 + 2 * x - 5) = x - 1
      rw [h_eq]
      have h1 : ((sqrt 113 - 5) / 4) ^ 2 + 2 * ((sqrt 113 - 5) / 4) - 5 < 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (113 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (113 : ℝ) by norm_num)]
      rw [show abs (((sqrt 113 - 5) / 4) ^ 2 + 2 * ((sqrt 113 - 5) / 4) - 5) = - (( (sqrt 113 - 5) / 4) ^ 2 + 2 * ((sqrt 113 - 5) / 4) - 5) by
        rw [abs_of_neg h1]
      ]
      field_simp
      <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (113 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (113 : ℝ) by norm_num)]
    · -- Show that x < sqrt 2
      rw [h_eq]
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (113 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (113 : ℝ) by norm_num), sq_nonneg ((sqrt 113 - 5) / 4 - sqrt 2)]