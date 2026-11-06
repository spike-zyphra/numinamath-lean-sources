import Mathlib

theorem algebra_95384 (x y a b : ℕ) (h1 : x < 100) (hx : x = 10 * a + b) (hy : y = 10 * b + a) (h2 : x + 5 = 2 * (y + 5)): x - y = 18 := by
  subst hx
  subst hy
  -- Now Lean needs to solve the arithmetic goal with constraints
  omega