import Mathlib

theorem number_theory_168149 (n : ℕ) (hn : n > 7) :
    ∃ m k, n = 3*m + 5*k := by
  have h2 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
    omega
  rcases h2 with (h | h | h)
  · -- n % 3 = 0
    use n / 3, 0
    omega
  · -- n % 3 = 1
    use (n - 10) / 3, 2
    omega
  · -- n % 3 = 2
    use (n - 5) / 3, 1
    omega