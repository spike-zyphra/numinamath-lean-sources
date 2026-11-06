import Mathlib

theorem algebra_244947 {t : ℝ → ℝ} (ht : t = fun l => 2 * Real.pi * Real.sqrt (l / g)) :
    ∃ c, ∀ l, t l = c * Real.sqrt (l / g) := by
  use 2 * Real.pi 
  intro l 
  rw [ht]
  all_goals ring 
  all_goals ring
  all_goals ring 
  all_goals ring