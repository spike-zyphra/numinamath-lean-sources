import Mathlib

open Nat Finset

/-The unit price of product A is 50 yuan, and the unit price of product B is 60 yuan. Several schools each paid 1220 yuan to purchase these two products, and the quantity of product A purchased by any 2 schools is different. Then, the maximum number of schools participating in this procurement is 4 schools.-/
def solset : Finset (ℕ × ℕ) := ((Finset.range 1000).product (Finset.range 1000)).filter fun ⟨x, y⟩ => 0 < x ∧ 0 < y ∧ 50 * x + 60 * y = 1220

theorem algebra_624533 : solset.card = 4 := by
  native_decide
