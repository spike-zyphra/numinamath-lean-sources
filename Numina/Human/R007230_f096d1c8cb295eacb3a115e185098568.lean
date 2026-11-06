import Mathlib

/-Cedric has deposited $\$12,\!000$ into an account that pays $5\%$ interest compounded annually.

Daniel has deposited $\$12,\!000$ into an account that pays $7\%$ simple annual interest.

In $15$ years Cedric and Daniel compare their respective balances. To the nearest dollar, what is the positive difference between their balances?-/
theorem algebra_13086 (cedric daniel : ℝ)
    (hcedric : cedric = 12000 * (1 + 0.05)^15)
    (hdaniel : daniel = 12000 * (1 + 0.07 * 15)) :
    round (cedric - daniel) = 347 := by
  rw [hcedric, hdaniel, round_eq]
  ring_nf
