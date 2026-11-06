import Mathlib

open Real

theorem algebra_95523 (x y z d : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
(h1: Real.logb 12 x - Real.logb 12 162 = d)
(h2: Real.logb 12 y - Real.logb 12 x = d)
(h3: Real.logb 12 z - Real.logb 12 y = d)
(h4: Real.logb 12 1250 - Real.logb 12 z = d)
: x = 270 := by

  have h5 : Real.logb 12 1250 - Real.logb 12 162 = 4 * d := by
    linarith

  have h6 : Real.logb 12 1250 - Real.logb 12 162 = Real.logb 12 (1250 / 162 : ℝ) := by
    rw [← Real.logb_div (by norm_num) (by norm_num)]
  
  have h7 : Real.logb 12 (1250 / 162 : ℝ) = 4 * Real.logb 12 (5 / 3 : ℝ) := by
    have h8 : (1250 / 162 : ℝ) = (5 / 3) ^ 4 := by
      norm_num
    rw [h8]
    have h9 : Real.logb 12 ((5 / 3 : ℝ) ^ 4) = 4 * Real.logb 12 (5 / 3 : ℝ) := by
      simp [Real.logb_pow]
    linarith

  have h11 : Real.logb 12 (5 / 3 : ℝ) = d := by
    have h10 : 4 * Real.logb 12 (5 / 3 : ℝ) = 4 * d := by
      have h11 : Real.logb 12 (1250 / 162 : ℝ) = 4 * d := by
        linarith [h5, h6]
      linarith [h7, h11]
    linarith

  have h12 : Real.logb 12 x = Real.logb 12 162 + d := by
    linarith

  have h13 : Real.logb 12 x = Real.logb 12 (162 * (5 / 3 : ℝ)) := by
    have h14 : Real.logb 12 (162 * (5 / 3 : ℝ)) = Real.logb 12 162 + Real.logb 12 (5 / 3 : ℝ) := by
      rw [Real.logb_mul (by norm_num) (by norm_num)]
    have h15 : Real.logb 12 (5 / 3 : ℝ) = d := by
      linarith [h11]

    rw [h14, h15] at *
    linarith [h12]

  have h16 : x = 162 * (5 / 3 : ℝ) := by
    apply Real.logb_injOn_pos (by norm_num) (Set.mem_Ioi.mpr hx) (Set.mem_Ioi.mpr (by norm_num)) h13

  norm_num at h16 ⊢
  all_goals try linarith