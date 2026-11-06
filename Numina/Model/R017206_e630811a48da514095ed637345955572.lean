import Mathlib

open Real Set

theorem algebra_20983 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (h : a + b + c + d = 1) :
    a^2 + b^2 + c^2 + d^2 ≤ 1 := by
  have h5 : a ^ 2 ≤ a := by
    nlinarith [ha, show a ≤ 1 by nlinarith [h, ha, hb, hc, hd]]
  have h6 : b ^ 2 ≤ b := by
    nlinarith [hb, show b ≤ 1 by nlinarith [h, ha, hb, hc, hd]]
  have h7 : c ^ 2 ≤ c := by
    nlinarith [hc, show c ≤ 1 by nlinarith [h, ha, hb, hc, hd]]
  have h8 : d ^ 2 ≤ d := by
    nlinarith [hd, show d ≤ 1 by nlinarith [h, ha, hb, hc, hd]]
  have h9 : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ≤ a + b + c + d := by
    linarith [h5, h6, h7, h8]
  linarith [h9, h]