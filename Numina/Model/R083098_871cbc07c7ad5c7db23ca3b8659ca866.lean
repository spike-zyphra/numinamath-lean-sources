import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_314874 (f g : ℝ → ℝ) (a b : ℝ)
  (hf : f = λ x => x^2 + 2 * b * x + 1) (hg : g = λ x => 2 * a * (x + b))
  (hfg : ¬∃ x, f x = g x) :
  (a^2 + b^2) < 1 := by 
  by_contra h
  push_neg at h
  have h3 : a^2 + b^2 ≥ 1 := by nlinarith
  have h4 : ∃ x : ℝ, f x = g x := by
    use (a - b + Real.sqrt (a^2 + b^2 - 1))
    simp [hf, hg]
    have h5 : a^2 + b^2 - 1 ≥ 0 := by nlinarith
    nlinarith [Real.sqrt_nonneg (a^2 + b^2 - 1), Real.sq_sqrt (show (0 : ℝ) ≤ a^2 + b^2 - 1 by nlinarith)]
  exact hfg h4