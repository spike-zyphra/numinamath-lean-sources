import Mathlib

theorem number_theory_109546 :
    IsLeast {n | n > 0 ∧ (Nat.digits 10 n).length > 0 ∧ (Nat.digits 10 n).toFinset.card = 1 ∧ 18 ∣ n} 666 := by
  constructor
  · -- First, we show 666 is in the set
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · native_decide
    · norm_num
  · -- Then, we need to show n ≥ 666 for all n in the set
    intro n hn
    rcases hn with ⟨hn_pos, hn_dig_len_pos, hn_all_id, hn_div⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at hn_pos hn_dig_len_pos hn_all_id hn_div <;> try { contradiction } <;> try { native_decide }
    all_goals contradiction