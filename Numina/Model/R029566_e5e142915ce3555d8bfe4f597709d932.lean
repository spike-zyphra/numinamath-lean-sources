import Mathlib

theorem number_theory_609861 :
    {n : ℕ | n ≤ 9 ∧ 91 ∣ 123450789 + 1000 * n} = {7} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume n in the set
    intro h
    rcases h with ⟨h1, h2⟩
    omega
  · -- Assume n = 7
    intro h
    rw [h]
    all_goals
      constructor <;> omega