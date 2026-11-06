import Mathlib
theorem algebra_605121 (x y z : ℝ) (hx : 0 < x ∧ x < 1) (hy : 0 < y ∧ y < 1) (hz : 0 < z ∧ z < 1) (h : x * y * z = (1 - x) * (1 - y) * (1 - z)) :
    max ((1 - x) * y) (max ((1 - y) * z) ((1 - z) * x)) ≥ 1 / 4 := by
  rcases hx with ⟨hx1, hx2⟩
  rcases hy with ⟨hy1, hy2⟩
  rcases hz with ⟨hz1, hz2⟩
  by_contra h1
  push_neg at h1
  have h2 : (1 - x) * y < 1 / 4 := by 
    have h3 : max ((1 - x) * y) (max ((1 - y) * z) ((1 - z) * x)) < 1 / 4 := h1
    have h4 : (1 - x) * y ≤ max ((1 - x) * y) (max ((1 - y) * z) ((1 - z) * x)) := by 
      simp [le_max_iff]
    linarith
  have h3 : (1 - y) * z < 1 / 4 := by 
    have h4 : max ((1 - y) * z) ((1 - z) * x) ≤ max ((1 - x) * y) (max ((1 - y) * z) ((1 - z) * x)) := by 
      simp [le_max_iff]
    have h5 : (1 - y) * z ≤ max ((1 - x) * y) (max ((1 - y) * z) ((1 - z) * x)) := by 
      have h6 : (1 - y) * z ≤ max ((1 - y) * z) ((1 - z) * x) := by 
        simp [le_max_iff]
      linarith
    linarith 
  have h4 : (1 - z) * x < 1 / 4 := by 
    have h4 : (1 - z) * x ≤ max ((1 - y) * z) ((1 - z) * x) := by 
      simp [le_max_iff]
    have h5 : max ((1 - y) * z) ((1 - z) * x) ≤ max ((1 - x) * y) (max ((1 - y) * z) ((1 - z) * x)) := by 
      simp [le_max_iff]
    have h6 : (1 - z) * x ≤ max ((1 - x) * y) (max ((1 - y) * z) ((1 - z) * x)) := by 
      linarith 
    linarith 
  nlinarith [mul_pos hx1 hy1, mul_pos hx1 hz1, mul_pos hy1 hz1, 
            mul_pos (sub_pos.mpr hx2) (sub_pos.mpr hy2), 
            mul_pos (sub_pos.mpr hx2) (sub_pos.mpr hz2), 
            mul_pos (sub_pos.mpr hy2) (sub_pos.mpr hz2)]