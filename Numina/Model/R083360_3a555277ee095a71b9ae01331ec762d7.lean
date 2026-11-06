import Mathlib

theorem algebra_222905 {n m : ℕ} (hn : n > 0) (hm : m > 0)
    (h1 : n = m) (h2 : n + 3 = 2 * (m - 3)) :
    n + m = 18 := by 
  omega