import Mathlib

open Finset

/-A single burger is not enough to satisfy a guy's hunger. The five guys go to Five Guys' Restaurant,
which has 20 different meals on the menu. Each meal costs a different integer dollar amount between $1 and $20.
The five guys have $20 to split between them, and they want to use all the money to order five different meals.
How many sets of five meals can the guys choose? -/

theorem combinatorics_608576: ((Icc 1 10 ×ˢ Icc 2 10 ×ˢ Icc 3 10 ×ˢ Icc 4 10 ×ˢ Icc 5 10).filter
  (fun (x, y, z, w, r) => x + y + z + w + r = 20 ∧ x < y ∧ y < z ∧ z < w ∧ w < r)).card = 7 := by

  native_decide