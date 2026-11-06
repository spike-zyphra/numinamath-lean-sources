import Mathlib

theorem number_theory_14496 : {d < 6 | 11 ∣ Nat.ofDigits 6 [5, d, d, 2]} = {4} := by
  ext d
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume d < 6 and 11 divides $2dd5_6$, prove d = 4
    intro h
    rcases h with ⟨h1, h2⟩
    interval_cases d <;> norm_num [Nat.ofDigits] at h2 <;> omega
  · -- Assume d = 4, prove d < 6 and 11 divides $2445_6$
    intro h
    rw [h]
    constructor
    · -- Show d < 6
      norm_num
    · -- Show 11 divides the number
      norm_num [Nat.ofDigits]