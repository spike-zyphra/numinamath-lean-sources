import Mathlib

theorem number_theory_13884 :
    IsLeast {n : ℕ | n > 100 ∧ Finset.lcm (Finset.Icc 1 n) id = Finset.lcm (Finset.Icc 101 n) id} 194 := by
  constructor
  · -- Show 194 is in the set
    constructor
    · -- Show 194 > 100
      norm_num
    · -- Show that the least common multiple of {1, ..., 194} is equal to that of {101, ..., 194}
      native_decide
  · -- Show that no smaller n is in the set
    intro n hn
    rcases hn with ⟨hn100, hneq⟩
    by_contra h
    push_neg at h
    have h1 : n ≤ 193 := by
      omega
    have h3 : Finset.lcm (Finset.Icc 1 n) id ≠ Finset.lcm (Finset.Icc 101 n) id := by
      interval_cases n <;> try { native_decide }
      <;> try { contradiction }
    contradiction