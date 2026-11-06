import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_159570 {f : ℝ → ℝ → ℝ} (hf : ∀ a b, f a b = sin a * cos b)
  (x y : ℝ) (h : f x y - f y x = 1) :
  f x y + f y x ≤ 1 := by 
  have hfx_y : f x y = sin x * cos y := hf x y
  have hfy_x : f y x = sin y * cos x := hf y x
  rw [hfx_y, hfy_x] at h 
  have hgoal : f x y + f y x = sin x * cos y + sin y * cos x := by 
    rw [hfx_y, hfy_x]
  rw [hgoal]
  have h1 : sin x * cos y + sin y * cos x = sin (x + y) := by 
    rw [sin_add]
    <;> ring
  rw [h1]
  have h2 : sin (x + y) ≤ 1 := by 
    apply sin_le_one
  linarith [h2]