import Mathlib

open Finset

theorem number_theory_242718 (a : ℕ → ℚ) (ha : a 0 = 0)
    (h : ∀ n, a (n + 1) = a n + 1 ∨ a (n + 1) = -1 / a n) :
    ∃ s : ℕ → ℚ, s 0 = 0 ∧ ∀ n, s (n + 1) = s n + 1 ∨ s (n + 1) = -1 / s n ∧
    s 3 = 0 := by

  use fun n => (0 : ℚ)
  constructor
  · -- Show that s 0 = 0
    norm_num
  · intro n
    simp
    all_goals try { norm_num }
    all_goals try { tauto }