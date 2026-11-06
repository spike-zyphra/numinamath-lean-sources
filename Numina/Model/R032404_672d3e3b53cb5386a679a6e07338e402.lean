import Mathlib

theorem number_theory_64416 :
    IsLeast {N | 0 < N ∧ 19 ∣ N ∧ (Nat.digits 10 N).length > 0 ∧
      36 ∣ Nat.ofDigits 10 (List.reverse (Nat.digits 10 N))} 2394 := by
  constructor
  · -- Show 2394 in the set.
    constructor
    · norm_num -- 0 < 2394
    constructor
    · norm_num -- 19 ∣ 2394
    constructor
    · -- Show that (Nat.digits 10 2394).length > 0
      norm_num
    · -- Show that 36 divides the reversed digits.
      native_decide
  · -- Show there is no smaller N in the set.
    intro N h
    rcases h with ⟨hN_pos, hN_div19, hN_digit, hN_revdiv36⟩
    by_contra h
    push_neg at h
    interval_cases N <;> norm_num at hN_div19 hN_pos hN_revdiv36 hN_digit <;> all_goals try { contradiction }