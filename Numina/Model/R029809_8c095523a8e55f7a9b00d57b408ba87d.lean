import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_271159 : {x : ℝ | abs (x + 2) ≥ abs x} = Set.Ici (-1) := by 
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_Ici]
  constructor
  · -- Assume abs (x + 2) ≥ abs x, we need to prove x ≥ -1
    intro h
    by_cases h1 : x ≥ 0
    · -- x ≥ 0
      rw [abs_of_nonneg (show x + 2 ≥ 0 by linarith), abs_of_nonneg (show x ≥ 0 by linarith)] at h
      linarith
    by_cases h2 : x + 2 ≥ 0
    · -- x + 2 ≥ 0, so -2 ≤ x < 0
      rw [abs_of_nonneg (show x + 2 ≥ 0 by linarith), abs_of_neg (show x < 0 by linarith)] at h
      linarith
    · -- x + 2 < 0, so x < -2
      rw [abs_of_neg (show x + 2 < 0 by linarith), abs_of_neg (show x < 0 by linarith)] at h
      linarith
  · -- Assume x ≥ -1, we need to prove abs (x + 2) ≥ abs x
    intro h
    by_cases h1 : x ≥ 0
    · -- x ≥ 0
      rw [abs_of_nonneg (show x + 2 ≥ 0 by linarith), abs_of_nonneg (show x ≥ 0 by linarith)]
      linarith
    by_cases h2 : x + 2 ≥ 0
    · -- x + 2 ≥ 0, so -2 ≤ x < 0
      rw [abs_of_nonneg (show x + 2 ≥ 0 by linarith), abs_of_nonpos (show x ≤ (0 : ℝ) by linarith)]
      linarith
    · -- x + 2 < 0, so x < -2
      linarith