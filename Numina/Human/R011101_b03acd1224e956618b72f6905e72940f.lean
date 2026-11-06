import Mathlib

/- Three aluminum cans can be recycled to make a new can. How many new cans can eventually be made from 243 aluminum cans? (Remember that the first new cans that are made can then be recycled into even newer cans!)  Do not include the original 243 cans in your count. -/
theorem algebra_12425 {x : ℕ} (hx : x = 243) :
    (x / 3) + (x / 3^2) + (x / 3^3) + (x / 3^4) + (x / 3^5)  = 121 := by
  rw [hx]; norm_num