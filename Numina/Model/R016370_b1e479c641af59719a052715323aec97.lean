import Mathlib

open Real

theorem calculus_22237 (A B C D E F G H : ℝ × ℝ)
    (hA : A = (4, 7)) (hB : B = (7, 4)) (hC : C = (-4 / 7, 1))
    (hD : D = (1, 7 / 4)) (hE : E = (14, -8)) (hF : F = (-12, 21))
    (hG : G = (-2, -7 / 2)) (hH : H = (-1 / 3, 7 / 12)) :
    (C ∈ {(x, y) | y = -7 / 4 * x}) ∧ (F ∈ {(x, y) | y = -7 / 4 * x}) ∧
    (H ∈ {(x, y) | y = -7 / 4 * x}) := by
  constructor
  · -- Show that C is in the set
    rw [hC]
    simp
    <;> norm_num
  constructor
  · -- Show that F is in the set
    rw [hF]
    simp
    <;> norm_num
  · -- Show that H is in the set
    rw [hH]
    simp
    <;> norm_num