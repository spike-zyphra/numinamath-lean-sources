import Mathlib

open Finset

theorem algebra_240307 {a b c d : ℝ}
    (ha : a = max 10 8) (hb : b = min 10 8) (hc : c = max 11 13) (hd : d = min 11 13) :
    (b - 6) * (c + 15) = 56 := by
  rw [hb, hc]
  norm_num