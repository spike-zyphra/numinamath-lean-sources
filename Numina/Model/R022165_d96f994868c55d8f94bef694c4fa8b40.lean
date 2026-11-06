import Mathlib

theorem number_theory_159932 (n : ℕ) (hn : n > 27) :
    ∃ k m, n = 5 * k + 8 * m := by
  have h1 : n ≥ 28 := by omega
  have h2 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
    omega
  rcases h2 with (h | h | h | h | h)
  · -- Case where n % 5 = 0
    use n / 5, 0
    omega
  · -- Case where n % 5 = 1
    have h3 : n % 5 = 1 := h
    use (n - 16) / 5, 2
    omega
  · -- Case where n % 5 = 2
    use (n - 8 * 4) / 5, 4
    omega
  · -- Case where n % 5 = 3
    use (n - 8 * 1) / 5, 1
    omega
  · -- Case where n % 5 = 4
    use (n - 8 * 3) / 5, 3
    omega