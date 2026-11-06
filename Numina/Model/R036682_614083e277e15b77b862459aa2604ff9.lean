import Mathlib

theorem number_theory_609210 : 
  -- The largest positive integer expressible as a 2013-digit base -4 number
  let N := (16^1007 - 1) / 5;
  -- Its remainder when divided by 210 is 51
  N % 210 = 51 := by 
  norm_num