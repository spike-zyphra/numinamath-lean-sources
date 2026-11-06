import Mathlib

theorem algebra_21465 :
    IsLeast {n | 0 < n ∧ n > 1 ∧ Nat.Coprime n (∏ i ∈ Finset.range 20, (i + 1))} 23 := by
  constructor
  · -- We verify that 23 belongs to the given set
    constructor
    · -- 0 < 23
      norm_num
    constructor
    · -- 23 > 1
      norm_num
    · -- Check that gcd(23, 20!) = 1
      native_decide
  · -- We prove that 23 is the smallest element in the set
    intro n hn
    rcases hn with ⟨hn_pos, hn_gt1, hn_coprime⟩
    
    by_contra h
    push_neg at h
    interval_cases n <;> try { contradiction }
    <;> try { native_decide }