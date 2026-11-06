import Mathlib

def f (n : ℕ) : ℕ := if Even n then n / 2 else n + 5

theorem number_theory_177546 {n : ℕ} (hn : n > 1) :
    ∃ k, f^[k] n = 1 ↔ n = 2 ∨ n = 3 := by
  by_cases h2 : n = 2
  · -- Assume n = 2
    use 1
    simp [h2, f]
    all_goals omega
  · -- Case where n ≠ 2
    by_cases h3 : n = 3
    · -- Assume n = 3
      use 4
      simp [h3, f, Nat.odd_iff, Nat.even_iff]
      all_goals omega
    · -- Case where n ≠ 2 and n ≠ 3.
      use 0
      simp at *
      all_goals omega
  all_goals omega