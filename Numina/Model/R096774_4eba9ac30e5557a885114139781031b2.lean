import Mathlib

open Real

theorem calculus_4203 (f : ℝ → ℝ) (hf : f = arctan) : deriv f = fun x => 1 / (1 + x ^ 2) := by 
  rw [hf]
  funext x
  simp [Real.deriv_arctan]