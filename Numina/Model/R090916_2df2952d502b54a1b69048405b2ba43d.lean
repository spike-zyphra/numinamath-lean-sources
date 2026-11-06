import Mathlib

theorem number_theory_6306 (x : ℤ) (hx : x ≡ 3 [ZMOD 7]) (h6x : 6 * x ≡ 10 [ZMOD 8]) :
    x ≡ 3 [ZMOD 56] ∨ x ≡ 31 [ZMOD 56] := by
  norm_num [Int.ModEq] at hx h6x ⊢
  omega