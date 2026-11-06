import Mathlib

theorem algebra_155914 {a b p q : ℝ × ℝ}
    (ha : a = 6 * p - q)
    (hb : b = p + 2 * q)
    (hp : ‖p‖ = 8)
    (hq : ‖q‖ = 1 / 2)
    (h : Real.pi / 3 = Real.arccos (p.1 * q.1 + p.2 * q.2) / (‖p‖ * ‖q‖)) :
    ‖a.1 * b.2 - a.2 * b.1‖ = 26 * Real.sqrt 3 := by
  have h21 : ‖p‖ * ‖q‖ = 4 := by
    rw [hp, hq]
    norm_num
  have h23 : Real.arccos (p.1 * q.1 + p.2 * q.2) = 4 * Real.pi / 3 := by 
    field_simp [h21] at h 
    nlinarith 
  have h3 : Real.arccos (p.1 * q.1 + p.2 * q.2) ≤ Real.pi := by 
    apply Real.arccos_le_pi 
  have h4 : 4 * Real.pi / 3 > Real.pi := by
    nlinarith [Real.pi_pos]
  have h5 : Real.arccos (p.1 * q.1 + p.2 * q.2) ≤ Real.pi := by
    apply Real.arccos_le_pi
  linarith [h23, h3, Real.pi_pos, h4]