import Mathlib
open Real
/-
A customer who intends to purchase an appliance has three coupons, only one of which may be used:
Coupon 1: 10% off the listed price if the listed price is at least $50
Coupon 2: Itextdollar20 off the listed price if the listed price is at least $100
Coupon 3: 18% off the amount by which the listed price exceeds $100
For which of the following listed prices will coupon 1 offer a greater price reduction than either coupon 2 or coupon 3?
(A) $179.95 (B) $199.95 (C) $219.95 (D) $239.95 (E) $259.95-/
theorem algebra_94594 {x : ℝ} (hx : x ≥ 100) :
(1 - 10 / 100) * x > (1 - 20 / 100) * x ∧ (1 - 10 / 100) * x > (1 - 18 / 100) * (x - 100) := by
-- obtaining the result by normalizing the inequalities to their standard forms
constructor <;> linarith