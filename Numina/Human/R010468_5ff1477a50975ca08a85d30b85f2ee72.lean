import Mathlib

/- A store increased the original price of a shirt by a certain percent and then lowered the new price by the same amount.
Given that the resulting price was 84% of the original price, by what percent was the price increased and decreased?
(A) 16(B) 20(C) 28(D) 36(E) 40 -/
theorem algebra_93808 {x : ℝ} (hx : x > 0) (h : (1 + x / 100) * (1 - x / 100) = 0.84) :
x = 40 := by
--The claim is just about applying arithmetic to the hypothesis h
  ring_nf at h
  nlinarith