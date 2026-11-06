import Mathlib

theorem algebra_21587 : {n : ℕ | 0 < n ∧ n < 100 ∧ 3 ∣ n ∧ 4 ∣ n}.encard = 8 := by
  have h1 : {n : ℕ | 0 < n ∧ n < 100 ∧ 3 ∣ n ∧ 4 ∣ n} = {12, 24, 36, 48, 60, 72, 84, 96} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume 0 < n < 100 and 3 divides n and 4 divides n
      rintro ⟨h0, h100, h3, h4⟩
      interval_cases n <;> omega
    · -- Assume n ∈ {12, 24, 36, 48, 60, 72, 84, 96}
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      all_goals
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard]
  <;> rfl