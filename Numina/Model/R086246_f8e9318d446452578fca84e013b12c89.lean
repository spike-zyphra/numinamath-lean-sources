import Mathlib

theorem number_theory_408 :
    IsLeast {n : ℕ | n ≠ 0 ∧ 25 ∣ n ∧ 25 ∣ (Nat.digits 10 n).sum} 4975 := by
  constructor
  · -- First Prove that 4975 is in the set.
    constructor
    · norm_num -- 4975 ≠ 0
    constructor
    · norm_num -- 25 divides 4975
    · norm_num -- 25 divides the sum of the digits (4 + 9 + 7 + 5)
  · -- Now prove that 4975 is the least element
    intro n hn
    rcases hn with ⟨hnne0, hn1, hn2⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at hn1 hn2 <;> norm_num at hnne0 hn1 hn2 <;> try { contradiction }
    <;> omega