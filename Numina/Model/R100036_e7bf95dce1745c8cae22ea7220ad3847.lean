import Mathlib

open Real

theorem calculus_17005 (v : ℝ × ℝ) (h : v = (0, 4)) :
    let u := (1, 3)
    let t := (v.1 * u.1 + v.2 * u.2) / (u.1 ^ 2 + u.2 ^ 2)
    (2 * t * u.1 - v.1, 2 * t * u.2 - v.2) = (12 / 5, 16 / 5) := by 
  rw [h]
  norm_num