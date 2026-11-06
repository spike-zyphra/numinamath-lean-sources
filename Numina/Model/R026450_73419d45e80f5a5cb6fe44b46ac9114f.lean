import Mathlib

theorem algebra_160150 {x : ℝ} (hx : x = 2) :
    ((x + Real.sqrt 3) / (Real.sqrt x + Real.sqrt (x + Real.sqrt 3)) +
     (x - Real.sqrt 3) / (Real.sqrt x - Real.sqrt (x - Real.sqrt 3))) = Real.sqrt 2 := by
  rw [hx]
  have h1 : Real.sqrt (2 : ℝ) > 0 := by
    apply Real.sqrt_pos.mpr
    norm_num
  have h2 : Real.sqrt 3 > 0 := by
    apply Real.sqrt_pos.mpr
    norm_num
  have h3 : Real.sqrt (2 + Real.sqrt 3) = (Real.sqrt 3 + 1) / Real.sqrt 2 := by
    have h1' : Real.sqrt (2 + Real.sqrt 3) = (Real.sqrt 3 + 1) / Real.sqrt 2 := by
      have h2 : ((Real.sqrt 3 + 1) / Real.sqrt 2) ^ 2 = (2 + Real.sqrt 3 : ℝ) := by
        field_simp [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by linarith)]
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith)]
      have h3_pos : 0 ≤ (Real.sqrt 3 + 1) / Real.sqrt 2 := by
        apply div_nonneg
        · -- Show Real.sqrt 3 + 1 ≥ 0
          linarith [Real.sqrt_nonneg 3]
        · -- Show Real.sqrt 2 > 0
          linarith [show Real.sqrt (2 : ℝ) > 0 by apply Real.sqrt_pos.mpr; linarith]
      rw [← h2]
      field_simp
      all_goals nlinarith [Real.sqrt_nonneg 3]
    exact h1'
  have h4 : Real.sqrt (2 - Real.sqrt 3) = (Real.sqrt 3 - 1) / Real.sqrt 2 := by
    have h1' : Real.sqrt (2 - Real.sqrt 3) = (Real.sqrt 3 - 1) / Real.sqrt 2 := by
      have h2 : ((Real.sqrt 3 - 1) / Real.sqrt 2) ^ 2 = (2 - Real.sqrt 3 : ℝ) := by
        field_simp [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by linarith)]
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith)]
      have h3_pos : 0 ≤ (Real.sqrt 3 - 1) / Real.sqrt 2 := by
        apply div_nonneg
        · -- Show Real.sqrt 3 - 1 ≥ 0
          nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by linarith)]
        · -- Show Real.sqrt 2 > 0
          linarith [show Real.sqrt (2 : ℝ) > 0 by apply Real.sqrt_pos.mpr; linarith]
      rw [← h2]
      field_simp
    exact h1'
  have h5 : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by linarith)
  have h6 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by linarith)
  rw [h3, h4]
  have h8 : Real.sqrt (2 : ℝ) + (Real.sqrt 3 + 1) / Real.sqrt (2 : ℝ) = (3 + Real.sqrt 3) / Real.sqrt 2 := by
    field_simp
    <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by linarith), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by linarith)]
  have h9 : Real.sqrt (2 : ℝ) - (Real.sqrt 3 - 1) / Real.sqrt (2 : ℝ) = (3 - Real.sqrt 3) / Real.sqrt 2 := by
    field_simp
    <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by linarith), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by linarith)]
  rw [h8, h9]
  have h12 : (2 + Real.sqrt 3) / ((3 + Real.sqrt 3) / Real.sqrt 2) + (2 - Real.sqrt 3) / ((3 - Real.sqrt 3) / Real.sqrt 2) = Real.sqrt 2 := by
    have h13 : 0 < (3 + Real.sqrt 3 : ℝ) := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith)]
    have h14 : 0 < (3 - Real.sqrt 3 : ℝ) := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith)]
    field_simp [h13, h14, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by linarith)]
    <;> nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith), mul_pos (Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by linarith)) (Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by linarith))]
  linarith [h12]