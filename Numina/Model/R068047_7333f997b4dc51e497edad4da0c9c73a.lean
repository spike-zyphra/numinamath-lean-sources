import Mathlib

theorem number_theory_13876 {n m p : ℕ} (hn : n > 0) (hm : m > 0) (hp : p > 0)
    (h1 : n * 4 = m * 3 + p * 12) (h2 : m * 4 = n * 3 + p * 12) (h3 : p * 4 = n * 3 + m * 12)
    (h4 : n + m + p = 408) :
    n + m + p = 408 := by
  exact h4