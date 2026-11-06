import Mathlib

theorem inequalities_54311 (x y z : ℝ) (hx : 0 < x ∧ x < 1) (hy : 0 < y ∧ y < 1) (hz : 0 < z ∧ z < 1)
    (h : x * y * z = (1 - x) * (1 - y) * (1 - z)) :
    max (max ((1 - x) * y) ((1 - y) * z)) ((1 - z) * x) ≥ 1 / 4 := by
  rcases hx with ⟨hx0, hx1⟩
  rcases hy with ⟨hy0, hy1⟩
  rcases hz with ⟨hz0, hz1⟩
  by_contra h
  have h_lt : max (max ((1 - x) * y) ((1 - y) * z)) ((1 - z) * x) < 1 / 4 := by 
    simpa using h
  have h2 : (1 - x) * y < 1 / 4 := by 
    have h2' : (1 - x) * y ≤ max (max ((1 - x) * y) ((1 - y) * z)) ((1 - z) * x) := by 
      simp [max_le_iff]
    linarith [h_lt, h2']
  have h3 : (1 - y) * z < 1 / 4 := by 
    have h3' : (1 - y) * z ≤ max (max ((1 - x) * y) ((1 - y) * z)) ((1 - z) * x) := by 
      simp [max_le_iff]
    linarith [h_lt, h3']
  have h4 : (1 - z) * x < 1 / 4 := by 
    have h4' : (1 - z) * x ≤ max (max ((1 - x) * y) ((1 - y) * z)) ((1 - z) * x) := by 
      simp [max_le_iff]
    linarith [h_lt, h4']
  nlinarith [mul_pos hx0 hy0, mul_pos hy0 hz0, mul_pos hz0 hx0, 
          mul_pos (sub_pos.mpr hx0) (sub_pos.mpr hy0), 
          mul_pos (sub_pos.mpr hy0) (sub_pos.mpr hz0), 
          mul_pos (sub_pos.mpr hz0) (sub_pos.mpr hx0),
          mul_pos (sub_pos.mpr hx1) (sub_pos.mpr hy1), 
          mul_pos (sub_pos.mpr hy1) (sub_pos.mpr hz1), 
          mul_pos (sub_pos.mpr hz1) (sub_pos.mpr hx1)]