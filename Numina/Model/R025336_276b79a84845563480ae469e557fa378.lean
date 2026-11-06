import Mathlib

theorem number_theory_116019 (n : ℕ) (hn : n > 7) :
    ∃ x y, n = 3*x + 5*y := by
  have h1 : n > 7 := hn
  have h2 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
    omega
  rcases h2 with (h | h | h)
  · -- Case 1: n ≡ 0 (mod 3)
    use n / 3, 0
    omega
  · -- Case 2: n ≡ 1 (mod 3)
    use (n - 10) / 3, 2
    omega
  · -- Case 3: n ≡ 2 (mod 3)
    use (n - 5) / 3, 1
    omega