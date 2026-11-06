import Mathlib

open Real

theorem calculus_147421 (K : ℝ → ℝ → ℝ) (hK : K = fun x t => x * exp t) (a b : ℝ)
    (ha : a = 0) (hb : b = 1) :
    ∃ R, R = fun x lambda => x * exp (lambda * x) / (1 - lambda) := by 
  refine ⟨fun x lambda => x * exp (lambda * x) / (1 - lambda), rfl⟩