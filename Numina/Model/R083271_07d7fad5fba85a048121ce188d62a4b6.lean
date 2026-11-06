import Mathlib

theorem algebra_161697 (C F : ℝ) (hC : C = (F - 32) / 1.8) :
    C = F ↔ C = -40 := by
  constructor
  · -- Assume C = F, prove C = -40
    intro h
    rw [h] at hC
    norm_num at hC ⊢
    linarith
  · -- Assume C = -40, prove C = F
    intro h
    have hF : F = -40 := by
      rw [h] at hC
      norm_num at hC ⊢
      linarith
    rw [h, hF]