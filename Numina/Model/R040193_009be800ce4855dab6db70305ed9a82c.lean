import Mathlib

theorem number_theory_10773 : ∑ᶠ (x : ℕ) (_ : x < 100 ∧ x % 25 = 3 ∧ x % 10 = 8), x = 106 := by
  have h1 : {x : ℕ | x < 100 ∧ x % 25 = 3 ∧ x % 10 = 8} = {28, 78} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, 
              and_imp]
    constructor
    · -- First, show that if $x$ satisfies all three conditions, then $x$ must be either 28 or 78.
      intro h
      rcases h with ⟨h1, h2, h3⟩
      interval_cases x <;> omega
    · -- Show that if $x$ is either 28 or 78, then it satisfies all three conditions.
      rintro (rfl | rfl)
      · -- Case x = 28
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- Case x = 78
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
  rw [show ∑ᶠ (x : ℕ) (_ : x < 100 ∧ x % 25 = 3 ∧ x % 10 = 8), x = ∑ᶠ (x ∈ {x : ℕ | x < 100 ∧ x % 25 = 3 ∧ x % 10 = 8}), x by rfl]
  rw [h1]
  rw [finsum_mem_pair]
  <;> norm_num