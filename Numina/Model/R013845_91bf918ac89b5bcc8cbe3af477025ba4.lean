import Mathlib

theorem algebra_1363 (C F : ℝ) (hC : C = (5 / 9) * (F - 32)) (hF : F = (9 / 5) * C + 32) :
C = F ↔ C = -40 := by 
  constructor
  · -- Assume C = F, prove C = -40
    intro h_eq 
    have h1 : C = (9 / 5) * C + 32 := by
      linarith [h_eq, hF]
    linarith 
  · -- Assume C = -40, prove C = F
    intro h_eq 
    have h1 : F = -40 := by
      rw [h_eq] at hF
      linarith 
    linarith [h1, h_eq]