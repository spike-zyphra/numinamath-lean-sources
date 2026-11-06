import Mathlib

theorem number_theory_67977 {n : ℕ} (hn : n ≥ 1000 ∧ n < 2000)
    (h1 : n % 2 = 1) (h2 : n % 3 = 1) (h3 : n % 4 = 1) (h4 : n % 5 = 1)
    (h5 : n % 6 = 1) (h6 : n % 7 = 1) (h7 : n % 8 = 1) :
    n % 41 = 0 := by
  rcases hn with ⟨hn1, hn2⟩
  interval_cases n <;> omega