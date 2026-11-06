import Mathlib

theorem algebra_235928 {x : ℝ} (hx : x = Real.sqrt 3 / 2) :
    (1 + x) / (1 + Real.sqrt (1 + x)) + (1 - x) / (1 - Real.sqrt (1 - x)) = 1 := by
  have h1 : x = Real.sqrt 3 / 2 := hx
  have h2 : 1 + x = (2 + Real.sqrt 3) / 2 := by
    rw [h1]
    ring
  have h2' : 1 - x = (2 - Real.sqrt 3) / 2 := by
    rw [h1]
    ring
  have h3 : Real.sqrt (1 + x) = (Real.sqrt 3 + 1) / 2 := by
    rw [h2]
    have h4 : Real.sqrt ((2 + Real.sqrt 3) / 2) = (Real.sqrt 3 + 1) / 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
    exact h4
  have h5 : Real.sqrt (1 - x) = (Real.sqrt 3 - 1) / 2 := by
    rw [h2']
    have h6 : Real.sqrt ((2 - Real.sqrt 3) / 2) = (Real.sqrt 3 - 1) / 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
    exact h6
  have h7 : (1 + x) / (1 + Real.sqrt (1 + x)) = (2 + Real.sqrt 3) / (3 + Real.sqrt 3) := by
    rw [h3]
    have h8 : (1 + x) = (2 + Real.sqrt 3) / 2 := h2
    rw [h8]
    have h9 : 1 + ((Real.sqrt 3 + 1) / 2 : ℝ) = (3 + Real.sqrt 3) / 2 := by
      ring_nf
    rw [h9]
    field_simp
    <;> ring
  have h10 : (1 - x) / (1 - Real.sqrt (1 - x)) = (2 - Real.sqrt 3) / (3 - Real.sqrt 3) := by
    rw [h5]
    have h11 : (1 - x) = (2 - Real.sqrt 3) / 2 := h2'
    rw [h11]
    have h12 : (1 - ((Real.sqrt 3 - 1) / 2 : ℝ)) = (3 - Real.sqrt 3) / 2 := by
      ring_nf
    rw [h12]
    field_simp
    <;> ring
  rw [h7, h10]
  field_simp [(show 3 + Real.sqrt 3 ≠ 0 by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  ), (show 3 - Real.sqrt 3 ≠ 0 by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  )]
  <;> nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]