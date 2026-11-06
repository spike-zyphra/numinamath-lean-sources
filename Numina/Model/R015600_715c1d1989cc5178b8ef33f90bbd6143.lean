import Mathlib

theorem number_theory_159641 :
    Set.ncard {x | x > 0 ∧ x ∣ (10^100 : ℕ) ∧ x ∣ (10^121 + 10^813 + 10)} = 4 := by
  have h1 : {x | x > 0 ∧ x ∣ (10^100 : ℕ) ∧ x ∣ (10^121 + 10^813 + 10)} = {1, 2, 5, 10} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume x is in the left side. Show it is in {1, 2, 5, 10}.
      intro h
      rcases h with ⟨hx_pos, hx1, hx2⟩
      have h2 : x ∣ 10 := by
        have h3 : x ∣ Nat.gcd (10^100) (10^121 + 10^813 + 10) := by
          exact Nat.dvd_gcd hx1 hx2
        have h4 : Nat.gcd (10^100) (10^121 + 10^813 + 10) = 10 := by
          norm_num [Nat.gcd]
        rw [h4] at h3
        exact h3
      have h3 : x ≤ 10 := by
        exact Nat.le_of_dvd (by norm_num) h2
      interval_cases x <;> norm_num at hx_pos h2 hx1 hx2 ⊢
    · -- Assume x is in {1, 2, 5, 10}. Show it is in the left side.
      rintro (rfl | rfl | rfl | rfl)
      · -- x = 1
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- x = 2
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- x = 5
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- x = 10
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
  rw [h1]
  norm_num