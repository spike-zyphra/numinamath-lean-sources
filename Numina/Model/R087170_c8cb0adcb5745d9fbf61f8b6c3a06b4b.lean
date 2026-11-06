import Mathlib

theorem number_theory_212654 {x y : ℕ} (hx : x > 0) (hy : y > 0)
    (h1 : x * 10 + 1 = 489) (h2 : x * 10 + 7 = 147) :
    x = 21 ∧ y = 10 := by
  omega