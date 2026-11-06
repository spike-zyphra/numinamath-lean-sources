import Mathlib

theorem number_theory_13512 : IsLeast {x : ℕ | 0 < x ∧ (2025 : ℤ) ∣ Nat.factorial x} 10 := by
  constructor
  · -- Show 10 is in the set.
    constructor
    · norm_num
    · -- Show that 2025 divides 10!
      native_decide
  · -- Show that 10 is the smallest such.
    intro y hy
    rcases hy with ⟨hy_pos, hy_div⟩
    by_contra h
    push_neg at h
    interval_cases y <;> try { contradiction }
    <;> try { contradiction }