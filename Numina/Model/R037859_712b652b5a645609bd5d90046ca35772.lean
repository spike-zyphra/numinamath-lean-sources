import Mathlib

theorem number_theory_196295 :
    {a : ℕ | (a ∈ Finset.Icc 100 999) ∧ 7 ∣ (504000 + a) ∧ 9 ∣ (504000 + a) ∧ 11 ∣ (504000 + a)} = {504} := by
  ext a
  simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- First direction: if a satisfies all these conditions, then a=504
    rintro ⟨⟨ha1, ha2⟩, h7, h9, h11⟩
    interval_cases a <;> norm_num at h7 h9 h11 ⊢ <;> omega
  · -- Second direction: if a=504, then all conditions are satisfied
    intro h
    rw [h]
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num