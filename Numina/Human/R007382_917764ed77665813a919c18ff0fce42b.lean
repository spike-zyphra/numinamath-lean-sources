import Mathlib

/- Luke is borrowing $\$10{,}000$ from the bank. The bank offers him a choice between two $10$-year payment plans:

${\bf Plan~1.}$  Luke's debt accumulates $10\%$ annual interest which compounds quarterly. Luke pays off half his balance after $5$ years, and the rest at the end of the $10$ years.

${\bf Plan~2.}$  Luke's debt accumulates $10\%$ annual interest which compounds annually. Luke pays off his full balance at the end of the $10$ years.

What is the (positive) difference between Luke's total payments under Plan 1 and his total payments under Plan 2? Round to the nearest dollar.-/
theorem algebra_13209 {P r : ℝ} (hP : P = 10000) (hr : r = 0.1) :
    ⌊(P * (1 + r) ^ 10 - (P * (1 + r / 4) ^ 20 / 2) * (1 + (1 + r / 4) ^ 20) + 1 / 2: ℝ)⌋ = 4319 := by
  -- ⌊x + 1 / 2⌋ equals to the nearest integer of x.
  rw [hP, hr]
  norm_num
