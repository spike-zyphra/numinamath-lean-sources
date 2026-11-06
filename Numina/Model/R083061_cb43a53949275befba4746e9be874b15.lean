import Mathlib

open Real Set
open scoped BigOperators

/- Given the set $A=\left{ x\left| \left( ax-1 \right)\left( a-x \right)>0 \right. \right}$, and $2\in A$, $3\notin A$, then the range of the real number $a$ is ___          ___. -/
theorem algebra_12608 {a : ℝ} (A : Set ℝ)
  (hA : A = {x | (a * x - 1) * (a - x) > 0}) (ha : 2 ∈ A) (hb : 3 ∉ A) :
  1 / 3 ≤ a ∧ a < 1 / 2 ∨ 2 < a ∧ a ≤ 3 := by
  rw [hA] at ha hb
  simp at ha hb
  by_cases h1 : a < 1 / 2
  · -- Assume a < 1/2
    have h3 : 1 / 3 ≤ a := by nlinarith
    left
    exact ⟨h3, h1⟩
  · -- Assume a ≥ 1/2
    have h2 : a ≥ 1 / 2 := by linarith
    have h3 : a > 2 := by nlinarith
    have h4 : a ≤ 3 := by nlinarith
    right
    exact ⟨h3, h4⟩