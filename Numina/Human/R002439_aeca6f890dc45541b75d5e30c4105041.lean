import Mathlib

/- Cagney can frost a cupcake every 20 seconds and Lacey can frost a cupcake every 30 seconds. Working together, 
how many cupcakes can they frost in 5 minutes?
(A) 10 (B) 15 (C) 20 (D) 25 (E) 30-/

theorem algebra_93416 (x : ℕ) (hx : x = 5 * 60) :
(x / 20) + (x / 30) = 25 := by {
  -- Substitute in x and evaluate.
  rw [hx]
}