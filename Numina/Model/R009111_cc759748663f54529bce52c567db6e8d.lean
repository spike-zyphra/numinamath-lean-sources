import Mathlib

theorem number_theory_6309 (x : ℤ) (h1 : 23 * x ≡ 1 [ZMOD 140]) (h2 : 17 * x ≡ 229 [ZMOD 1540]) :
    x ≡ 557 [ZMOD 1540] := by
  norm_num [Int.ModEq] at h1 h2 ⊢
  omega