import Mathlib

theorem algebra_8140 (beijing_time new_york_time : ℝ) (h₀ : beijing_time = 18) (h₁ : new_york_time = beijing_time - 13) : new_york_time = 5 := by
  rw [h₀] at h₁
  linarith  -- Solving the linear arithmetic goal new_york_time = 18 - 13 = 5