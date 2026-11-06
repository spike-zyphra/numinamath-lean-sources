import Mathlib

/- Which of the following integers are divisible by 11?
a) 10763732
b) 1086320015
c) 674310976375
d) 8924310064537-/
theorem number_theory_4747 :
    ¬11 ∣ 10763732 ∧
    11 ∣ 1086320015 ∧
    ¬11 ∣ 674310976375 ∧
    ¬11 ∣ 8924310064537 := by
  -- verify by computation
  split_ands <;> norm_num
