import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_160810 {f : ℝ → ℝ} (hf : StrictMono f)
  (hP : P = {x | x = f x}) (hQ : Q = {x | x = f (f x)}) :
  P = Q := by
  ext x 
  simp [hP, hQ]
  constructor
  · -- Assume $x = f x$, need to show $f (f x) = x$
    intro h
    have h1 : f x = x := by linarith 
    have eq1 : f (f x) = x := by 
      have h4 : f x = x := by linarith [h, h1] 
      simp [h4]
    linarith [h1, eq1]
  · -- Assume $f (f x) = x$, need to show $x = f x$
    intro h
    by_cases h1 : x < f x 
    · -- Assume x < f x 
      have h2 : f x < f (f x) := by 
        apply hf.lt_iff_lt.2 
        linarith 
      have h3 : f (f x) = x := by linarith 
      have h4 : f x < x := by 
        linarith [h3, h2] 
      linarith 
    · -- x >= f x 
      by_cases h2 : x > f x 
      · -- Assume x > f x 
        have h3 : f x > f (f x) := by 
          apply hf.lt_iff_lt.2 
          linarith 
        have h4 : f (f x) = x := by linarith 
        have h5 : f x > x := by 
          linarith [h4, h3] 
        linarith 
      · -- Assume x ≤ f x 
        have h3 : x = f x := by 
          linarith 
        linarith