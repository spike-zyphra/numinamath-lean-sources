import Mathlib

theorem algebra_59239 (V1 V2 : ℝ) (hV1 : V1 = 50.0) (hV2 : V2 = 75.0)
    (hM1 hM2 : ℝ) (hM1' : hM1 = 0.200) (hM2' : hM2 = 0.100) :
    (hM1 * V1 + hM2 * V2) / (V1 + V2) = 0.140 := by 
  rw [hV1, hV2, hM1', hM2']
  norm_num