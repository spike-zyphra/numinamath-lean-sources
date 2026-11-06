import Mathlib

theorem number_theory_197249 (n : ℕ) (hn : n > 7) :
    ∃ x y, n = 3*x + 5*y := by
  have h1 : n > 7 := hn
  have h3 : n ≥ 8 := by omega
  have h4 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h4 with (h | h | h)
  · -- n % 3 = 0
    use n / 3, 0
    omega
  · -- n % 3 = 1
    use (n - 10) / 3, 2
    omega
  · -- n % 3 = 2
    use (n - 5) / 3, 1
    omega