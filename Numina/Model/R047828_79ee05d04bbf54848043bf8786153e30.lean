import Mathlib

theorem number_theory_266091 (n : ℕ) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p * (p + 1) + q * (q + 1) = n * (n + 1) ↔
    (n = 2 ∧ p = 2 ∧ q = 3) ∨ (n = 3 ∧ p = 5 ∧ q = 6) := by

  use 0, 0
  simp
  all_goals
    try { norm_num }
    all_goals
      try { tauto }