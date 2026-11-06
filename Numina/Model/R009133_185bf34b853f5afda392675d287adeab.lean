import Mathlib

theorem algebra_16322 : {x : ℕ | x ∣ 96 ∧ 12 ∣ x}.ncard = 4 := by
  have h1 : {x : ℕ | x ∣ 96 ∧ 12 ∣ x} = {12, 24, 48, 96} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume x divides 96 and is divisible by 12, show x is in {12, 24, 48, 96}
      intro h
      rcases h with ⟨h1, h2⟩
      have h3 : x ≤ 96 := by 
        exact Nat.le_of_dvd (by norm_num) h1
      interval_cases x <;> norm_num at h1 h2 <;> tauto
    · -- Assume x is in {12, 24, 48, 96}, show x divides 96 and is divisible by 12
      rintro (rfl | rfl | rfl | rfl)
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try native_decide