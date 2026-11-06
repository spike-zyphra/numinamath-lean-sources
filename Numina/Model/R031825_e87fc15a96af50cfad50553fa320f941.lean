import Mathlib

theorem algebra_20287 (radius : ℝ) (hr : radius = 9) (speed : ℝ) (h : speed * 3 = 2 * (2 * π * radius)) :
    speed = 12 * π := by
  rw [hr] at h 
  have eq1 : speed * 3 = 2 * (2 * π * (9 : ℝ)) := h 
  have eq2 : speed * 3 = 36 * π := by 
    calc
      speed * 3 = 2 * (2 * π * (9 : ℝ)) := h 
      _ = 2 * (18 * π) := by ring 
      _ = 36 * π := by ring
  have eq3 : speed = 12 * π := by
    linarith
  exact eq3