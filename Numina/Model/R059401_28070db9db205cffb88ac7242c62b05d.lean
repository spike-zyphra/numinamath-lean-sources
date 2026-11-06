import Mathlib

theorem algebra_315643 (x : ℝ) (hx : x > 0) (h : (60 * 0.8 + (x - 60) * 1.2) / x = 0.88) :
    60 * 0.8 + (x - 60) * 1.2 = 66 := by 
  have h1 : 60 * 0.8 + (x - 60) * 1.2 = 0.88 * x := by
    have h2 : x ≠ 0 := by linarith
    field_simp at h ⊢
    linarith
  have hx_eq : x = 75 := by
    ring_nf at h1 
    linarith 
  rw [hx_eq]
  norm_num