import Mathlib

theorem other_178037 (R1 R2 : ℝ) (hR1 : R1 = 10) (hR2 : R2 = 20)
    (h : (1 / R1 + 1 / R2) * 1.5 = 1 / (R1 + R2)) :
    R1 + R2 = 10 := by
  rw [hR1, hR2] at h
  norm_num at h ⊢
  <;> linarith