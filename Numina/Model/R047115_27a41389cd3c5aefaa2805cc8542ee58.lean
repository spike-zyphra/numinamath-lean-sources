import Mathlib

theorem number_theory_324870 :
    Set.ncard {n : ℕ | 1 ≤ n ∧ n ≤ 100 ∧ Nat.gcd (n^2 + 4) (n + 3) > 1} = 7 := by
  have h1 : {n : ℕ | 1 ≤ n ∧ n ≤ 100 ∧ Nat.gcd (n^2 + 4) (n + 3) > 1} = 
            {10, 23, 36, 49, 62, 75, 88} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Forward implication: if n is in the set, then n must be in {10, 23, 36, 49, 62, 75, 88}
      intro h
      rcases h with ⟨h1, h2, h3⟩
      interval_cases n <;> norm_num [Nat.gcd] at h3 ⊢ <;> tauto
    · -- Backward implication: if n is in {10, 23, 36, 49, 62, 75, 88}, then n is in the set
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- Verify that 10 is in the set
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num [Nat.gcd]
      · -- Verify that 23 is in the set
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num [Nat.gcd]
      · -- Verify that 36 is in the set
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num [Nat.gcd]
      · -- Verify that 49 is in the set
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num [Nat.gcd]
      · -- Verify that 62 is in the set
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num [Nat.gcd]
      · -- Verify that 75 is in the set
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num [Nat.gcd]
      · -- Verify that 88 is in the set
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num [Nat.gcd]
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp
  <;> try { native_decide }