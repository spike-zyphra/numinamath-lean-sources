import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_170526 {f : ℝ → ℝ} (hf : StrictMono f)
  (h_one_to_one : Function.Injective f) (P Q : Set ℝ)
  (hP : P = {x | f x = x}) (hQ : Q = {x | f (f x) = x}) :
  P = Q := by
  ext x
  simp [hP, hQ]
  constructor
  · -- Assume f x = x, prove f (f x) = x
    intro h
    rw [show f x = x by linarith]
    all_goals linarith
  · -- Assume f (f x) = x, prove f x = x
    intro h
    have h1 : f (f x) = x := h
    by_cases h2 : f x > x
    · -- Case where f x > x
      have h4 : f (f x) > f x := by apply hf.lt_iff_lt.mpr; linarith
      linarith [h1, h4, h2]
    · -- Case where f x ≤ x
      by_cases h3 : f x < x
      · -- Case where f x < x
        have h5 : f (f x) < f x := by apply hf.lt_iff_lt.mpr; linarith
        linarith [h1, h5, h3]
      · -- Case where f x = x
        have h4 : f x = x := by linarith
        linarith [h4]