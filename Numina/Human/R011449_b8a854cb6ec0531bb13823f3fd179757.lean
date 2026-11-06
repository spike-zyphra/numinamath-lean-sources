import Mathlib

/- A cell phone plan costs 20 dollars each month, plus 5 cents per text message sent, plus 10 cents for each minute used over 30 hours. In January Michelle sent 100 text messages and talked for 30.5 hours. How much did she have to pay?
(A) 24.00(B) 24.50(C) 25.50(D) 28.00(E) 30.00 -/
theorem algebra_94488 (messages minutes: ℝ) (hx : messages = 100) (hy : minutes = 30.5) :
20 + 0.05 * messages + 0.10 * (minutes - 30) * 60 = 28 := by
    --we substitute in the formula the number of minutes and messages
    rw[hx, hy]
    --we conclude by an algbraic calculation
    norm_num