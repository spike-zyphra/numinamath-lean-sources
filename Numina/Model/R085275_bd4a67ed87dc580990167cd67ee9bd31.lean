import Mathlib

theorem algebra_237298 (x : ℕ) (hx : x ≥ 2) (h : (5 * x + 1) = x * (x + 4)) :
    x + 4 = 5 := by
  nlinarith -- solve arithmetic goals, especially with contradiction in the hypothesis