import Mathlib

theorem algebra_283982 {x : ℝ} (hx : x = 1 / (2 - Real.sqrt 3)) :
    x^6 - 2 * Real.sqrt 3 * x^5 - x^4 + x^3 - 4 * x^2 + 2 * x - Real.sqrt 3 = 2 := by
  have h1 : x = 2 + Real.sqrt 3 := by 
    rw [hx]
    have h2 : 2 - Real.sqrt 3 ≠ 0 := by 
      nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
    field_simp [h2, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
    <;> nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
  rw [h1]
  have h2 : (2 + Real.sqrt 3) ^ 2 = 7 + 4 * Real.sqrt 3 := by
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
  have h3 : (2 + Real.sqrt 3) ^ 3 = 26 + 15 * Real.sqrt 3 := by
    calc
      (2 + Real.sqrt 3) ^ 3 = (2 + Real.sqrt 3) * ((2 + Real.sqrt 3) ^ 2) := by ring
      _ = (2 + Real.sqrt 3) * (7 + 4 * Real.sqrt 3) := by rw [h2]
      _ = 26 + 15 * Real.sqrt 3 := by nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
  have h4 : (2 + Real.sqrt 3) ^ 4 = 97 + 56 * Real.sqrt 3 := by
    calc
      (2 + Real.sqrt 3) ^ 4 = (2 + Real.sqrt 3) * ((2 + Real.sqrt 3) ^ 3) := by ring
      _ = (2 + Real.sqrt 3) * (26 + 15 * Real.sqrt 3) := by rw [h3]
      _ = 97 + 56 * Real.sqrt 3 := by nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
  have h5 : (2 + Real.sqrt 3) ^ 5 = 362 + 209 * Real.sqrt 3 := by
    calc
      (2 + Real.sqrt 3) ^ 5 = (2 + Real.sqrt 3) * ((2 + Real.sqrt 3) ^ 4) := by ring
      _ = (2 + Real.sqrt 3) * (97 + 56 * Real.sqrt 3) := by rw [h4]
      _ = 362 + 209 * Real.sqrt 3 := by nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
  have h6 : (2 + Real.sqrt 3) ^ 6 = 1351 + 780 * Real.sqrt 3 := by
    calc
      (2 + Real.sqrt 3) ^ 6 = (2 + Real.sqrt 3) * ((2 + Real.sqrt 3) ^ 5) := by ring
      _ = (2 + Real.sqrt 3) * (362 + 209 * Real.sqrt 3) := by rw [h5]
      _ = 1351 + 780 * Real.sqrt 3 := by nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
  nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), h2, h3, h4, h5, h6]
  all_goals nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
  all_goals nlinarith
  all_goals nlinarith [sq_nonneg (Real.sqrt 3), sq_nonneg (2 : ℝ), sq_nonneg ((2 + Real.sqrt 3) * (2 + Real.sqrt 3)), sq_nonneg ((2 - Real.sqrt 3) * (2 + Real.sqrt 3)), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)]
  all_goals nlinarith [Real.sqrt_nonneg 3, Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
  all_goals nlinarith [sq_nonneg ((2 + Real.sqrt 3) * (15) ), sq_nonneg ((56) * (Real.sqrt 3)), sq_nonneg ((15) * (2 + Real.sqrt 3) - 4), sq_nonneg ((56) * (2 + Real.sqrt 3) - 15) ]
  all_goals nlinarith [ sq_nonneg ((2 + Real.sqrt 3) ) ]