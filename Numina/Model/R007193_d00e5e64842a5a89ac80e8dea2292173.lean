import Mathlib

theorem number_theory_4747 :
    ¬11 ∣ 10763732 ∧
    11 ∣ 1086320015 ∧
    ¬11 ∣ 674310976375 ∧
    ¬11 ∣ 8924310064537 := by
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  · norm_num