import Mathlib

/-The product of the digits of a 5 -digit number is 180 . How many such numbers exist?-/

theorem combinatorics_611153:
  ((Finset.Icc 1 9 ×ˢ Finset.range 10 ×ˢ Finset.range 10 ×ˢ Finset.range 10 ×ˢ Finset.range 10).filter
  (fun (x, y, z, w, r) => x * y * z * w * r = 180)).card = 360 := by

  native_decide