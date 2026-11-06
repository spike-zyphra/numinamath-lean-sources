import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_326988 {f g : ℝ → ℝ}
  (hf : f = λ x => arccos x) (hg : g = λ x => -cos x)
  (hfg : ∀ x, f (-x) = g x) :
  ∀ x, g (-x) = f x := by
    intro x
    have h0 := hfg 0
    simp [hf, hg] at h0 ⊢
    all_goals
      linarith [Real.pi_pos]