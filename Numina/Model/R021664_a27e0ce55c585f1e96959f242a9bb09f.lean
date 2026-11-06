import Mathlib

theorem algebra_323259 {a b : ℝ} (ha : a = ⌊1 / (3 - Real.sqrt 7)⌋) (hb : b = 1 / (3 - Real.sqrt 7) - a) :
    a^2 + (1 + Real.sqrt 7) * a * b = 10 := by

  have h1 : 1 / (3 - Real.sqrt 7) = (3 + Real.sqrt 7) / 2 := by
    have h2 : 3 - Real.sqrt 7 ≠ 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 7 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]
    field_simp [h2, sq, mul_comm]
    <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 7 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]

  have h3 : ⌊1 / (3 - Real.sqrt 7)⌋ = 2 := by
    rw [h1]
    have h4 : 2 < (3 + Real.sqrt 7) / 2 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 7 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]
    have h5 : (3 + Real.sqrt 7) / 2 < 3 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 7 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> nlinarith

  have ha2 : a = (2 : ℝ) := by
    rw [ha]
    exact_mod_cast h3

  have hb2 : b = (Real.sqrt 7 - 1) / 2 := by
    rw [hb, ha2]
    have h1' : 1 / (3 - Real.sqrt 7) = (3 + Real.sqrt 7) / 2 := by
      have h2 : 3 - Real.sqrt 7 ≠ 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 7 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]
      field_simp [h2, sq, mul_comm]
      <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 7 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]
    rw [h1']
    linarith

  rw [ha2, hb2]
  nlinarith [sq_nonneg (Real.sqrt 7), Real.sqrt_pos.mpr (show (0 : ℝ) < 7 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]