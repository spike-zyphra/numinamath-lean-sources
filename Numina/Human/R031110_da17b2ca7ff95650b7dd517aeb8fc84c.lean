import Mathlib
/-When Lauren was born on January 1, 1990, her grandparents put $\$1000$ in a savings account in her name. The account earned $7.5\%$ annual interest compounded quarterly every three months. To the nearest dollar, how much money was in her account when she turned two?-/
theorem algebra_21415 (P : ℝ) (r : ℝ) (t : ℝ) (hP : P = 1000) (hr : r = 0.075) (ht : t = 2) :
    round (P * (1 + r / 4) ^ (4 * t)) = 1160 := by
    rw[hP,hr,ht,round_eq]
    norm_num
