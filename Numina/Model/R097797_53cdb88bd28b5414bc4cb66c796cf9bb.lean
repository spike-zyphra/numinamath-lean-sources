import Mathlib

theorem number_theory_16580 : 2011 * 2012 * 2013 * 2014 ≡ 4 [ZMOD 5] := by 
  norm_num [Int.ModEq]