import Mathlib

theorem algebra_21681 (P Q B C D : ℝ) (hP : P = 8) (hQ : Q = 48)
    (hB : B = (P + Q) / 2) (hC : C = (B + Q) / 2) (hD : D = (P + C) / 2) :
    D = 23 := by
  rw [hP, hQ] at hB
  have hB2 : B = 28 := by
    linarith
  rw [hB2, hQ] at hC
  have hC2 : C = 38 := by
    linarith
  rw [hP, hC2] at hD
  linarith