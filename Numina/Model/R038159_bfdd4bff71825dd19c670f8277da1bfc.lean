import Mathlib

theorem algebra_20607 : {p | p.Prime ∧ p ∣ 117 * 119}.encard = 4 := by
  have h1 : {p | p.Prime ∧ p ∣ 117 * 119} = {3, 7, 13, 17} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- First direction: if p is prime and divides 117 * 119, then p ∈ {3, 7, 13, 17}
      intro h
      rcases h with ⟨h_prime, hdiv⟩
      have h4 : p ∣ 117 ∨ p ∣ 119 := by
        have h9 : p ∣ 117 * 119 := hdiv
        have h10 : p ∣ 117 ∨ p ∣ 119 := by
          apply (Nat.Prime.dvd_mul h_prime).1
          all_goals try tauto
        tauto
      rcases h4 with (h7 | h7)
      · -- Case where p divides 117
        have h8 : p ≤ 117 := by
          exact Nat.le_of_dvd (show 0 < 117 by norm_num) h7
        interval_cases p <;> norm_num at h_prime h7 <;> tauto
      · -- Case where p divides 119
        have h8 : p ≤ 119 := by
          exact Nat.le_of_dvd (show 0 < 119 by norm_num) h7
        interval_cases p <;> norm_num at h_prime h7 <;> tauto
    · -- Second direction: if p ∈ {3,7,13,17}, then p is prime and divides 117 * 119
      rintro (rfl | rfl | rfl | rfl)
      · -- p = 3
        constructor
        · norm_num
        · norm_num
      · -- p = 7
        constructor
        · norm_num
        · norm_num
      · -- p = 13
        constructor
        · norm_num
        · norm_num
      · -- p = 17
        constructor
        · norm_num
        · norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> try { tauto }