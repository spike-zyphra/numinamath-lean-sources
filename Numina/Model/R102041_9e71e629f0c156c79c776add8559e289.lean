import Mathlib

open Real

theorem calculus_22024 (v1 v2 : ℝ × ℝ)
    (h1 : v1 = (1, -2)) (h2 : v2 = (8, 1)) :
    let c := (v1.1 * v2.1 + v1.2 * v2.2) / (v2.1 ^ 2 + v2.2 ^ 2)
    (c * v2.1, c * v2.2) = (48 / 65, 6 / 65) := by
  rw [h1, h2]
  norm_num