import Mathlib

theorem number_theory_34669 : {x : ℕ | x < 125 ∧ (x ^ 3 - 2 * x + 6) % 125 = 0}.encard = 1 := by
  have h1 : {x : ℕ | x < 125 ∧ (x ^ 3 - 2 * x + 6) % 125 = 0} = {46} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · -- Assume x ∈ {x : ℕ | x < 125 ∧ (x ^ 3 - 2 * x + 6) % 125 = 0}, prove x=46
      intro h
      rcases h with ⟨h2, h3⟩
      interval_cases x <;> omega
    · -- Assume x=46, prove x ∈ {x : ℕ | x < 125 ∧ (x ^ 3 - 2 * x + 6) % 125 = 0}
      intro h
      rw [h]
      constructor
      · norm_num
      · norm_num
  rw [h1]
  simp [Set.encard_singleton]