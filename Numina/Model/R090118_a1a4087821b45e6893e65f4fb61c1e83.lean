import Mathlib

theorem algebra_274137 {x y : ℕ} (hx : x > y) (hy : y > 0)
    (hMegan : 42 = x * (n + 2) + y * n) (hShana : 35 = x * n + y * (n + 2))
    (hShana_wins : n = 2) : x = 4 := by
  subst hShana_wins 
  omega