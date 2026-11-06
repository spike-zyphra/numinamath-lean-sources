import Mathlib

open Real Set
open scoped BigOperators


theorem inequalities_254329 {f : ℝ → ℝ}
    (hf : Function.Injective f) (hinc : StrictMono f)
    (P Q : Set ℝ) (hP : P = {x | x > f x}) (hQ : Q = {x | x > f (f x)}) :
    P = Q := by
  rw [hP, hQ]
  ext x
  constructor
  · -- Assume x ∈ P: {x | x > f x}, prove x ∈ Q: {x | x > f (f x)}
    intro h
    have h1 : x > f x := by
      simpa using h
    have h2 : f x > f (f x) := by
      apply hinc
      linarith
    have h3 : x > f (f x) := by
      linarith
    simpa using h3
  · -- Assume x ∈ Q: {x | x > f (f x)}, prove x ∈ P: {x | x > f x}
    intro h
    have h4 : x > f (f x) := by
      simpa using h
    by_cases h7 : f x < x
    · -- If $f x < x$, then $f(f x) < f x$.
      have h8 : f x > f (f x) := by
        apply hinc
        linarith
      have h9 : x > f x := by
        linarith
      simpa using h9
    · -- Assume $\neg(f x < x)$, which means $f x ≥ x$.
      push_neg at h7
      have h8 : f (f x) >= f x := by
        apply hinc.monotone
        all_goals linarith
      have h9 : f x >= x := by 
        linarith
      have h10 : f (f x) >= x := by 
        linarith
      linarith