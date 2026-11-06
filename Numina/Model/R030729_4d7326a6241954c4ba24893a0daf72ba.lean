import Mathlib

theorem algebra_11711 :
    IsLeast {n | n ∈ Set.Icc 1000 9999 ∧ (Nat.digits 10 n).toFinset.card = 4 ∧ ∀ d ∈ (Nat.digits 10 n), n % d = 0} 1236 := by
  constructor
  · -- Show 1236 is in the set
    constructor
    · -- Show 1236 ∈ [1000, 9999]
      norm_num
    constructor
    · -- Show (Nat.digits 10 1236).toFinset.card = 4
      native_decide
    · -- Show ∀ d ∈ (Nat.digits 10 1236), 1236 % d = 0
      native_decide
  · -- Show 1236 is the minimal element in the set
    intro n hn
    rcases hn with ⟨hn1, hn2, hn3⟩
    rw [Set.mem_Icc] at hn1
    rcases hn1 with ⟨hn1l, hn1r⟩
    by_contra h
    push_neg at h
    have : n < 1236 := h
    interval_cases n <;> norm_num at hn2 hn3 ⊢ <;> all_goals try { contradiction }