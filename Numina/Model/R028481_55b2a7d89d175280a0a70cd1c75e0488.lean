import Mathlib

theorem number_theory_277564 :
  {n : ℕ | n ∈ Finset.Icc 100 999 ∧ n = 2 * (100 * (n % 10) + 10 * ((n / 10) % 10) + (n / 100)) - 1} = {793} := by
  ext n
  simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- First implication: if n satisfies the conditions, then n = 793
    rintro ⟨⟨hn1, hn2⟩, h⟩
    interval_cases n <;> norm_num at h hn1 hn2 ⊢
    <;> omega
  · -- Second implication: if n = 793, then it satisfies the conditions
    intro h
    rw [h]
    constructor
    · -- Show 793 is in the range [100, 999]
      norm_num
    · -- Verify the equation for 793
      norm_num