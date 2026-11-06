import Mathlib

theorem number_theory_19241 :
    IsLeast {a | 0 ≤ a ∧ a ≡ 2 [ZMOD 3] ∧ a ≡ 4 [ZMOD 5] ∧ a ≡ 6 [ZMOD 7] ∧ a ≡ 8 [ZMOD 9]} 314 := by
  constructor
  · -- Show 314 is in the set
    constructor
    · norm_num
    constructor
    · norm_num [Int.ModEq]
    constructor
    · norm_num [Int.ModEq]
    constructor
    · norm_num [Int.ModEq]
    · norm_num [Int.ModEq]
  · -- Show there is no smaller element in the set
    intro a ha
    rcases ha with ⟨ha0, ha1, ha2, ha3, ha4⟩
    by_contra h
    push_neg at h
    interval_cases a <;> norm_num [Int.ModEq] at ha1 ha2 ha3 ha4
    <;> omega