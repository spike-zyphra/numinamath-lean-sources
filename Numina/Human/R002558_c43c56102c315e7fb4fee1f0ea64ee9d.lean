import Mathlib

/- Suppose that the euro is worth 1.3 dollars. If Diana has 500 dollars and Etienne has 400 euros, by what percent is the value of Etienne's money greater that the value of Diana's money?
(A) 2(B) 4(C) 6.5(D) 8(E) 13 -/
theorem algebra_95419 (h : 1.3 * 400 > 500) :
((1.3:ℝ)  * 400 - 500) / 500 * 100 = 4 := by
    --it suffices to so apply linear arithmetic to find the equality
    ring