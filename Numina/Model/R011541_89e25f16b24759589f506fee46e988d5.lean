import Mathlib

theorem number_theory_627376 : ((2 ^ 859433) - 1) % 10 = 1 := by
  have h1 : (2 ^ 859433) % 10 = 2 := by
    norm_num
  omega