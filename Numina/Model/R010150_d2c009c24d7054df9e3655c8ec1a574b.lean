import Mathlib

theorem number_theory_275817 : {n : ℕ | n < 1000 ∧ 8 ∣ 764000 + n ∧ 9 ∣ 764000 + n ∧ 11 ∣ 764000 + n} = {280} := by
  ext n -- Consider an arbitrary natural number n
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume n satisfies all the conditions, we need to prove n = 280
    intro h
    rcases h with ⟨h1, h2, h3, h4⟩
    interval_cases n <;> omega
  · -- Assume n = 280, prove the divisibility conditions
    intro h
    rw [h]
    all_goals norm_num