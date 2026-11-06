import Mathlib
theorem number_theory_610952 : ⌊10000 / (9899 : ℝ) * 10 ^ 18⌋ ≡ 5 [ZMOD 10]:= by
  norm_num [Int.ModEq, Int.floor_eq_iff]