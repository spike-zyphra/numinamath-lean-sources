import Mathlib

open Real

theorem algebra_301004 {α : ℝ} (hα : α = (Real.sqrt 5 + 1) / 2) :
    ⌊α^16⌋ = 2206 := by
  have h1 : α^2 = α + 1 := by
    rw [hα]
    nlinarith [Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]
  have h4 : α^4 = 3 * α + 2 := by
    have h2 : α^2 = α + 1 := h1
    calc
      α^4 = (α^2)^2 := by ring
      _ = (α + 1)^2 := by rw [h2]
      _ = α^2 + 2 * α + 1 := by ring
      _ = (α + 1) + 2 * α + 1 := by rw [h2]
      _ = 3 * α + 2 := by ring
  have h8 : α^8 = 21 * α + 13 := by
    have h4' : α^4 = 3 * α + 2 := h4
    calc
      α^8 = (α^4)^2 := by ring
      _ = (3 * α + 2)^2 := by rw [h4']
      _ = 9 * α^2 + 12 * α + 4 := by ring
      _ = 9 * (α + 1) + 12 * α + 4 := by rw [h1]
      _ = 21 * α + 13 := by ring
  have h16 : α^16 = 987 * α + 610 := by
    have h8' : α^8 = 21 * α + 13 := h8
    calc
      α^16 = (α^8)^2 := by ring
      _ = (21 * α + 13)^2 := by rw [h8']
      _ = 441 * α^2 + 2 * 21 * 13 * α + 13^2 := by ring
      _ = 441 * (α + 1) + 546 * α + 169 := by
        rw [h1]
        <;> ring
      _ = 987 * α + 610 := by ring
  rw [h16]
  have h5 : 987 * α + 610 = (987 * Real.sqrt 5 + 2207) / 2 := by
    rw [hα]
    field_simp
    <;> ring_nf <;> norm_num [Real.sq_sqrt]
    <;> ring
  rw [h5]
  have h6 : 2205 < (987 : ℝ) * Real.sqrt 5 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num), Real.sqrt_le_sqrt (by norm_num : (16 : ℝ) ≤ (25 : ℝ)), Real.sqrt_le_sqrt (by norm_num : (9 : ℝ) ≤ (25 : ℝ)), Real.sq_sqrt (show 0 ≤ (16 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (9 : ℝ) by norm_num)]
  have h7 : (987 : ℝ) * Real.sqrt 5 < (2207 : ℝ) := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num), Real.sqrt_le_sqrt (by norm_num : (16 : ℝ) ≤ (25 : ℝ)), Real.sqrt_le_sqrt (by norm_num : (9 : ℝ) ≤ (25 : ℝ)), Real.sq_sqrt (show 0 ≤ (16 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (9 : ℝ) by norm_num)]
  have h8 : (2206 : ℝ) < (987 * Real.sqrt 5 + 2207) / 2 := by
    linarith
  have h9 : (987 * Real.sqrt 5 + 2207) / 2 < (2207 : ℝ) := by
    linarith
  rw [Int.floor_eq_iff]
  constructor
  · -- Show that 2206 < α^16
    linarith
  · -- Show that α^16 < 2207
    linarith