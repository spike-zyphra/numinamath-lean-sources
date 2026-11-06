import Mathlib

theorem number_theory_16681 (x : ℤ) (h : 3 * x + 7 ≡ 2 [ZMOD 16]) :
    2 * x + 11 ≡ 13 [ZMOD 16] := by
  norm_num [Int.ModEq] at h ⊢
  omega