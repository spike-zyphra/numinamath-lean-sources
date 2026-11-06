import Mathlib

theorem number_theory_102797 :
  ∑ᶠ n ∈ {n : ℕ | n < 50 ∧ Nat.gcd (4 * n + 5) (7 * n + 6) > 1}, n = 94 := by
  have h1 : {n : ℕ | n < 50 ∧ Nat.gcd (4 * n + 5) (7 * n + 6) > 1} = {7, 18, 29, 40} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · intro h
      rcases h with ⟨h1, h2⟩
      interval_cases n <;> try { tauto }
      <;> norm_num at h1 h2 <;> omega
    · rintro (rfl | rfl | rfl | rfl)
      · constructor <;> norm_num [Nat.gcd]
      · constructor <;> norm_num [Nat.gcd]
      · constructor <;> norm_num [Nat.gcd]
      · constructor <;> norm_num [Nat.gcd]
  rw [h1]
  rw [finsum_mem_eq_toFinset_sum]
  simp [Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
  <;> rfl