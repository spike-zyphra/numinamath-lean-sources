import Mathlib

theorem algebra_237787 (n : ℕ) :
    ∃ x : ℤ, n * x - 12 = 3 * n ↔ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 6 ∨ n = 12 := by
  by_cases h : n ≤ 12
  · -- n <= 12
    interval_cases n <;> norm_num
    <;> try { use 15; all_goals omega }
    <;> try { use 9; all_goals omega }
    <;> try { use 7; all_goals omega }
    <;> try { use 6; all_goals omega }
    <;> try { use 5; all_goals omega }
    <;> try { use 4; all_goals omega }
    <;> try { use 0; all_goals omega }
    <;> try { use 1; all_goals omega }
  · -- n > 12
    use 0
    simp at *
    <;> omega