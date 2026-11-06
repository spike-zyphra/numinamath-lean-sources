import Mathlib

theorem number_theory_275399 (k : ℕ) : ∃ n, k = 3 * n ∨ k = 3 * n + 1 ∨ k = 3 * n + 2 := by
  have h1 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by
    omega
  rcases h1 with (h1 | h1 | h1)
  · -- Case k % 3 = 0
    use k / 3
    omega
  · -- Case k % 3 = 1
    use k / 3
    omega
  · -- Case k % 3 = 2
    use k / 3
    omega