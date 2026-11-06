import Mathlib

theorem algebra_397 (c : ℝ) (f : ℝ → ℝ) (hf : f = fun x => x^2 - 5 * x + 3 * c) :
    f 3 = -12 ↔ c = -2 := by
  constructor
  · -- First implication: Assume f(3) = -12, rewrite in terms of c
    intro h
    simp [hf] at h
    linarith
  · -- Second implication: Assume c = -2, prove f(3) = -12
    intro h
    simp [hf, h]
    <;> linarith