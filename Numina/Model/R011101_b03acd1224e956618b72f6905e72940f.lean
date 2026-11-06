import Mathlib

theorem algebra_12425 {x : ℕ} (hx : x = 243) :
    (x / 3) + (x / 3^2) + (x / 3^3) + (x / 3^4) + (x / 3^5)  = 121 := by
  subst hx
  norm_num