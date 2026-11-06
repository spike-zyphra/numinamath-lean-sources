import Mathlib

theorem negated_number_theory_45938 :
    {n : ℕ | n ∈ Finset.Icc 100 999 ∧ n^2 = (Nat.digits 10 n).sum^5} = {243} := by
  ext n
  simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume n is in the left side set, we need to prove n is in the right side set
    intro h
    rcases h with ⟨⟨hn1, hn2⟩, hneq⟩
    interval_cases n <;> norm_num at hneq <;> norm_num
    <;> try { tauto }
  · -- Assume n is in the right side set, we need to prove it's in the left side set
    intro hneq
    rw [hneq]
    constructor
    · norm_num
    · norm_num