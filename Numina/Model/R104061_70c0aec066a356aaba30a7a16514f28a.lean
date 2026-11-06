import Mathlib

theorem number_theory_178855 :
    IsLeast {n | n ≥ 100000 ∧ 11 ∣ n ∧ (Nat.digits 10 n).length = 6 ∧
      (Nat.digits 10 n)[0]! + (Nat.digits 10 n)[3]! =
        (Nat.digits 10 n)[1]! + (Nat.digits 10 n)[4]! ∧
      (Nat.digits 10 n)[1]! + (Nat.digits 10 n)[4]! =
        (Nat.digits 10 n)[2]! + (Nat.digits 10 n)[5]!} 100122 := by
  constructor
  · -- Show 100122 is in the set
    constructor
    · norm_num -- verify 100122 >= 100000
    constructor
    · norm_num -- verify 11 divides 100122
    constructor
    · norm_num -- verify (Nat.digits 10 100122).length = 6 
      -- the digits of 100122 is [2, 2, 1, 0, 0, 1], so the length is 6
    constructor
    · -- verify (Nat.digits 10 100122)[0]! + (Nat.digits 10 100122)[3]! = (Nat.digits 10 100122)[1]! + (Nat.digits 10 100122)[4]!
      norm_num -- verify 2 + 1 = 0 + 0
    · -- verify (Nat.digits 10 100122)[1]! + (Nat.digits 10 100122)[4]! = (Nat.digits 10 100122)[2]! + (Nat.digits 10 100122)[5]!
      norm_num -- verify 0 + 0 = 1 + 2
  · -- Show there is no smaller element in the set
    intro n hn
    rcases hn with ⟨h1, h2, h3, h4, h5⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at h1 h2 h3 h4 h5 <;> all_goals contradiction