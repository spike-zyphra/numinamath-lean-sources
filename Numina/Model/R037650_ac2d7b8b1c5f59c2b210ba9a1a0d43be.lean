import Mathlib

theorem inequalities_9824 :
    Set.ncard {x : ℕ | x > 0 ∧ x^2 < 18 * x - 45} = 11 := by 
  have h1 : {x : ℕ | x > 0 ∧ x^2 < 18 * x - 45} = {4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume h: x > 0 ∧ x^2 < 18 * x - 45
      intro h
      rcases h with ⟨hx1, hx2⟩
      have h2 : x ≥ 4 := by
        by_contra h
        push_neg at h
        have : x < 4 := by linarith
        interval_cases x <;> omega
      have h3 : x ≤ 14 := by
        by_contra h
        push_neg at h
        have h4 : x ≥ 15 := by linarith
        have h5 : x^2 ≥ 18 * x - 45 := by
          have h6 : x ≥ 15 := h4
          have h7 : x^2 + 45 ≥ 18 * x := by nlinarith
          omega
        omega
      interval_cases x <;> tauto
    · -- Show x in {4,5,6,7,8,9,10,11,12,13,14} implies x in {x: ℕ | x > 0 ∧ x^2 < 18 * x - 45}
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
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
  <;> try { native_decide }