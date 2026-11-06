import Mathlib

/- Angela has deposited $\$8,\!000$ into an account that pays $6\%$ interest compounded annually.

Bob has deposited $\$10,\!000$ into an account that pays $7\%$ simple annual interest.

In $20$ years Angela and Bob compare their respective balances. To the nearest dollar, what is the positive difference between their balances? -/
theorem algebra_14711 (A B : ℝ) (hA : A = 8000) (hB : B = 10000)
    (hA' : A' = 0.06) (hB' : B' = 0.07) :
    round |A * (1 + A') ^ 20 - B * (1 + B' * 20)| = 1657 := by
  subst_vars
  norm_num [round_eq]
  simp [abs_of_pos]
  norm_num
