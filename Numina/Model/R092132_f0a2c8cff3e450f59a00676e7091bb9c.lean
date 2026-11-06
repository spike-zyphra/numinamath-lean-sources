import Mathlib

theorem number_theory_262570 :
    (Nat.digits 10 (Nat.lcm (Nat.lcm 20 16) 2016))[1]! = 8 := by
  norm_num