import Mathlib

theorem number_theory_22871 (a b : ℤ) (ha : a ≡ 16 [ZMOD 37]) (hb : b ≡ 21 [ZMOD 37]) :
    (a - b) ≡ 32 [ZMOD 37] := by 
  norm_num [Int.ModEq] at ha hb ⊢
  omega