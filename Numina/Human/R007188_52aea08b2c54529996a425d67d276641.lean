import Mathlib
open Mathlib
/--
Heather compares the price of a new computer at two different stores. Store $A$ offers $15\%$ off the sticker price followed by a $$90$ rebate, and store $B$ offers $25\%$ off the same sticker price with no rebate. Heather saves $$15$ by buying the computer at store $A$ instead of store $B$. What is the sticker price of the computer, in dollars?
-/

theorem algebra_1192 (p : ℚ)
  (h :
  let store_a_price : ℚ := (p * ((1 : ℚ) - ((15 : ℚ ) / 100 : ℚ))) - (90 : ℚ)
  let store_b_price : ℚ := p * ((1: ℚ ) - ((25 : ℚ) / 100 : ℚ))
  store_a_price = store_b_price - (15 : ℚ)) : p = 750 := by
    norm_num at *
    linarith