import Mathlib

theorem number_theory_196598 (n : ℕ) (h : n > 7) :
    ∃ k l, n = 3*k + 5*l := by
  have h1 : n ≥ 8 := by omega
  have h2 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
    omega
  rcases h2 with (h2 | h2 | h2)
  · -- Case n % 3 = 0
    use n / 3, 0
    omega
  · -- Case n % 3 = 1
    use (n - 10) / 3, 2
    omega
  · -- Case n % 3 = 2
    use (n - 5) / 3, 1
    omega