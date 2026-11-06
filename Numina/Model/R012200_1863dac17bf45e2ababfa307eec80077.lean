import Mathlib

theorem algebra_196772 {x y z : ℝ} (h : Real.arctan x + Real.arctan y + Real.arctan z = Real.pi / 2) :
    x * y + y * z + x * z = 1 := by
  have h1 : Real.cos (Real.arctan x + Real.arctan y + Real.arctan z) = 0 := by 
    rw [h]
    have : Real.cos (Real.pi / 2) = 0 := by 
      exact Real.cos_pi_div_two
    linarith
  have h2 : Real.cos (Real.arctan x + Real.arctan y + Real.arctan z) =
      (1 - x * y - y * z - x * z) / Real.sqrt ((1 + x^2) * (1 + y^2) * (1 + z^2)) := by
    have ha1 : Real.cos (Real.arctan x) = 1 / Real.sqrt (1 + x^2) := by
      rw [Real.cos_arctan]
      all_goals ring_nf <;> field_simp <;> ring
    have ha2 : Real.sin (Real.arctan x) = x / Real.sqrt (1 + x^2) := by
      rw [Real.sin_arctan]
      all_goals ring_nf <;> field_simp <;> ring
    have hb1 : Real.cos (Real.arctan y) = 1 / Real.sqrt (1 + y^2) := by
      rw [Real.cos_arctan]
      all_goals ring_nf <;> field_simp <;> ring
    have hb2 : Real.sin (Real.arctan y) = y / Real.sqrt (1 + y^2) := by
      rw [Real.sin_arctan]
      all_goals ring_nf <;> field_simp <;> ring
    have hc1 : Real.cos (Real.arctan z) = 1 / Real.sqrt (1 + z^2) := by
      rw [Real.cos_arctan]
      all_goals ring_nf <;> field_simp <;> ring
    have hc2 : Real.sin (Real.arctan z) = z / Real.sqrt (1 + z^2) := by
      rw [Real.sin_arctan]
      all_goals ring_nf <;> field_simp <;> ring
    have hangle : Real.cos (Real.arctan x + Real.arctan y + Real.arctan z) =
        Real.cos (Real.arctan x + Real.arctan y) * Real.cos (Real.arctan z) - Real.sin (Real.arctan x + Real.arctan y) * Real.sin (Real.arctan z) := by 
      rw [← Real.cos_add]
      all_goals ring
    have hangle2 : Real.cos (Real.arctan x + Real.arctan y) = Real.cos (Real.arctan x) * Real.cos (Real.arctan y) - Real.sin (Real.arctan x) * Real.sin (Real.arctan y) := by 
      rw [← Real.cos_add]
      all_goals ring
    have hangle3 : Real.sin (Real.arctan x + Real.arctan y) = Real.sin (Real.arctan x) * Real.cos (Real.arctan y) + Real.cos (Real.arctan x) * Real.sin (Real.arctan y) := by 
      rw [← Real.sin_add]
      all_goals ring
    rw [hangle, hangle2, hangle3, ha1, ha2, hb1, hb2, hc1, hc2]
    <;> field_simp <;> ring_nf <;> field_simp <;> ring
  rw [h2] at h1
  have h3 : Real.sqrt ((1 + x^2) * (1 + y^2) * (1 + z^2)) > 0 := by
    positivity
  have h4 : 1 - x * y - y * z - x * z = 0 := by 
    field_simp at h1 ⊢
    <;> nlinarith [Real.sqrt_pos.mpr (show (1 + x^2) * (1 + y^2) * (1 + z^2) > 0 by positivity)]
  nlinarith