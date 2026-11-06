import Mathlib

theorem algebra_13209 {P r : ℝ} (hP : P = 10000) (hr : r = 0.1) :
    ⌊(P * (1 + r) ^ 10 - (P * (1 + r / 4) ^ 20 / 2) * (1 + (1 + r / 4) ^ 20) + 1 / 2: ℝ)⌋ = 4319 := by
  rw [hP, hr]
  norm_num
  <;> try norm_num