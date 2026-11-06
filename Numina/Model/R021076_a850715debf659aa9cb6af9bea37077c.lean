import Mathlib

theorem inequalities_106867 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxyz : x < 1 ∧ y < 1 ∧ z < 1) (h : x * y * z = (1 - x) * (1 - y) * (1 - z)) :
    (1 / 4) ≤ max ((1 - x) * y) (max ((1 - y) * z) ((1 - z) * x)) := by
  have h1 : 0 < x := hx
  have h2 : 0 < y := hy
  have h3 : 0 < z := hz
  have hx1 : x < 1 := hxyz.1
  have hy1 : y < 1 := hxyz.2.1
  have hz1 : z < 1 := hxyz.2.2
  by_contra h7
  push_neg at h7
  have h8 : (1 - x) * y < (1 / 4 : ℝ) := by
    have h9 : max ((1 - x) * y) (max ((1 - y) * z) ((1 - z) * x)) < (1 / 4 : ℝ) := h7
    have h10 : (1 - x) * y ≤ max ((1 - x) * y) (max ((1 - y) * z) ((1 - z) * x)) := by 
      simp [max_le_iff]
    linarith
  have h9 : (1 - y) * z < (1 / 4 : ℝ) := by
    have h12 : max ((1 - x) * y) (max ((1 - y) * z) ((1 - z) * x)) < (1 / 4 : ℝ) := h7
    have h13 : (1 - y) * z ≤ max ((1 - x) * y) (max ((1 - y) * z) ((1 - z) * x)) := by 
      simp [max_le_iff]
    linarith
  have h10 : (1 - z) * x < (1 / 4 : ℝ) := by 
    have h14 : max ((1 - x) * y) (max ((1 - y) * z) ((1 - z) * x)) < (1 / 4 : ℝ) := h7
    have h15 : (1 - z) * x ≤ max ((1 - x) * y) (max ((1 - y) * z) ((1 - z) * x)) := by 
      simp [max_le_iff]
    linarith
  nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (y - 1 / 2), sq_nonneg (z - 1 / 2), 
      h, mul_pos hx hy, mul_pos hx hz, 
      mul_pos hy hz, mul_pos (sub_pos.mpr hx1) (sub_pos.mpr hy1), 
      mul_pos (sub_pos.mpr hx1) (sub_pos.mpr hz1), 
      mul_pos (sub_pos.mpr hy1) (sub_pos.mpr hz1), 
      mul_pos (show 0 < 1 - x by linarith) (show 0 < 1 - y by linarith), 
      mul_pos (show 0 < 1 - y by linarith) (show 0 < 1 - z by linarith), 
      mul_pos (show 0 < 1 - x by linarith) (show 0 < 1 - z by linarith)]