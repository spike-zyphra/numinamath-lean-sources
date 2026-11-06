import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_122782 (a : ℝ) :
  ∀ x : ℝ, ∃ y : ℝ, y = 1 / log (2 ^ x + 4 * 2 ^ (-x) - a) ↔ a < 3 := by

  intro x
  use if a < 3 then 1 / log (2 ^ x + 4 * 2 ^ (-x) - a) else (1 / log (2 ^ x + 4 * 2 ^ (-x) - a) + 1)
  split_ifs with ha
  · -- Assume a < 3, need to prove y = 1/log(...) ↔ a < 3
    simp [ha]
  · -- Assume a ≥ 3, need to prove y = 1/log(...) ↔ a < 3
    simp [ha]
    <;> norm_num at *
    <;> try { tauto }