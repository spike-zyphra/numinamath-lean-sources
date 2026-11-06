import Mathlib

theorem number_theory_105899 (x : ℤ) (h1 : x ≡ 1 [ZMOD 3]) (h2 : x ≡ -1 [ZMOD 5]) (h3 : x ≡ 2 [ZMOD 7]) (h4 : x ≡ -2 [ZMOD 11]) :
    x ≡ 394 [ZMOD 1155] := by
  norm_num [Int.ModEq] at h1 h2 h3 h4 ⊢
  omega