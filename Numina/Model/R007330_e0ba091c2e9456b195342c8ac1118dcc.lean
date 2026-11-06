import Mathlib

theorem algebra_11233 {l w : ℝ} (hl : l > 0) (hw : w > 0)
    (h : l * w = (l * 1.25) * (w * (1 - x))) :
    x = 0.2 := by
  have h_eq : l * w = (l * 1.25) * (w * (1 - x)) := h
  have hw' : (w) ≠ 0 := by linarith [hw]
  have hl' : (l) ≠ 0 := by linarith [hl]
  
  have h2 : 1 = 1.25 * (1 - x) := by
    apply (mul_left_inj' (show l ≠ 0 by linarith)).mp
    apply (mul_left_inj' (show w ≠ 0 by linarith)).mp
    ring_nf at h_eq ⊢
    nlinarith
  
  nlinarith