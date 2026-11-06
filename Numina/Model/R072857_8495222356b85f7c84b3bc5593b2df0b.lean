import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_142731 {K : ℝ} (hK : K > 0) (f : ℝ → ℝ)
  (hf : f = λ x => sqrt x) (g : ℝ → ℝ) (hg : g = λ x => -sqrt x)
  (hfg : ∀ x, f x = g (-x)) (h : ∫ x in (-1)..1, f x = 2 * K * (1 - π / 4)) :
  ∫ x in (-1)..1, f x = 2 * K * (1 - π / 4) := by 
  exact h