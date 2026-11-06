import Mathlib

theorem algebra_109804 {n m : ℕ} (hn : n > 0) (hm : m > 0)
    (h1 : n = 6 * (m + 1)) (h2 : n = 9 * (m - 1)) :
    n = 36 := by 
  omega