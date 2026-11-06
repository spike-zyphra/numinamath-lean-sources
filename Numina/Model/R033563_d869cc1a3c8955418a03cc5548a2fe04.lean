import Mathlib

theorem algebra_19757 {a b c d e f : ℤ} (ha : a = -4) (hb : b = 1) (hc : c = 1)
    (hd : d = 4) (he : e = 1) (hf : f = 1) :
    (a * x ^ 2 + b * x + c) * (d * x ^ 2 + e * x + f) =
    -16 * x ^ 4 + x ^ 2 + 2 * x + 1 := by
  subst_vars
  ring_nf