import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_233897 (a : ℝ) (f : ℝ → ℝ) (hf : f = λ x => x + 1)
  (h : ∀ x y, x ≤ a → f (x + y) ≤ 2 * f x - 3 * f y) :
  a ≤ -2 := by
  by_contra h1
  push_neg at h1
  have h1' : a > -2 := h1 
  have h2 := h (-2) 0 (by linarith)
  simp [hf] at h2
  all_goals nlinarith
  all_goals linarith