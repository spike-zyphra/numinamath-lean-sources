import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_17115 (t : ℝ) (ht : t ≠ 0) :
    (x, y) = ((t + 1)/t, (t - 1)/t) →
    y = -x + 2 := by
  intro h
  rcases h with ⟨rfl, rfl⟩
  field_simp [ht]
  <;> ring