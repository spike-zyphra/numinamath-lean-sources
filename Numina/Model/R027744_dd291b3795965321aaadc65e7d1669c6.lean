import Mathlib

open Real
open scoped BigOperators

theorem inequalities_43654 :
  (∀ a b c : ℕ, 0 < a → 0 < b → 0 < c → (1 / a + 1 / b + 1 / c < 1) → (1 / a + 1 / b + 1 / c ≤ 41 / 42)) ∧
  (∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (1 / a + 1 / b + 1 / c = 41 / 42)) := by
  constructor
  · intro a b c ha hb hc h
    omega
  · use 2, 3, 7
    all_goals
      norm_num