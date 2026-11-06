import Mathlib

theorem number_theory_3333 : {x : ℕ | ∃ y, x > 0 ∧ y > 0 ∧ 20 * x + 19 * y = 2240}.encard = 5 := by
  have h1 : {x : ℕ | ∃ y, x > 0 ∧ y > 0 ∧ 20 * x + 19 * y = 2240} = {17, 36, 55, 74, 93} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume there exists a positive y such that 20x + 19y = 2240
      rintro ⟨y, hx_pos, hy_pos, heq⟩
      omega
    · -- Assume x is in {17, 36, 55, 74, 93}, prove there exists a positive y such that 20x + 19y = 2240
      rintro (rfl | rfl | rfl | rfl | rfl)
      · -- x = 17
        exact ⟨100, by norm_num, by norm_num, by norm_num⟩
      · -- x = 36
        exact ⟨80, by norm_num, by norm_num, by norm_num⟩
      · -- x = 55
        exact ⟨60, by norm_num, by norm_num, by norm_num⟩
      · -- x = 74
        exact ⟨40, by norm_num, by norm_num, by norm_num⟩
      · -- x = 93
        exact ⟨20, by norm_num, by norm_num, by norm_num⟩
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> try { tauto }