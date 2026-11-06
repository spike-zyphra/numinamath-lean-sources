import Mathlib

  theorem algebra_188924 {n k : ℕ} (hn : n > 0) (h1 : n = 30 * k - 4) (h2 : n = 26 * (k + 9) - 6) :
  n = 1736 := by
  have eq1 : n + 4 = 30 * k := by
    omega
  have eq2 : n + 6 = 26 * (k + 9) := by
    omega
  have eq3 : k = 58 := by
    omega
  have eq4 : n = 1736 := by
    omega
  exact eq4