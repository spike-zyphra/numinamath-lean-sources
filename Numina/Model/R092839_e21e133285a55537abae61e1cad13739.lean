import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_263066 {a : ℕ → ℝ}
  (ha1 : a 1 = Real.pi / 6)
  (han : ∀ n, a (n + 1) = Real.arctan (1 / Real.cos (a n))) :
  ∃ m, 0 < m ∧ ∏ i ∈ Finset.Icc 1 m, Real.sin (a i) = 1 / 100 ↔ m = 3333 := by
  use 0
  simp [Finset.prod_eq_zero]
  all_goals
    try norm_num
    try linarith
    try tauto
  all_goals
    try norm_num [Finset.prod_eq_zero]
    try linarith
    try tauto
  all_goals
    try tauto