import Mathlib
open Mathlib
theorem algebra_1192 (p : ℚ)
  (h :
  let store_a_price : ℚ := (p * ((1 : ℚ) - ((15 : ℚ ) / 100 : ℚ))) - (90 : ℚ)
  let store_b_price : ℚ := p * ((1: ℚ ) - ((25 : ℚ) / 100 : ℚ))
  store_a_price = store_b_price - (15 : ℚ)) : p = 750 := by
    norm_num at h ⊢
    linarith