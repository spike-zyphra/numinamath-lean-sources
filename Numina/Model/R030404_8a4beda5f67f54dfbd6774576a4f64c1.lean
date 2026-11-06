import Mathlib

theorem number_theory_6730 : {x | x > 0 ∧ 2368 % x = 0}.encard = 14 := by
  have h1 : {x | x > 0 ∧ 2368 % x = 0} = {1, 2, 4, 8, 16, 32, 64, 37, 74, 148, 296, 592, 1184, 2368} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume x ∈ {x | x > 0 ∧ 2368 % x = 0}, prove x ∈ {1, 2, 4, 8, 16, 32, 64, 37, 74, 148, 296, 592, 1184, 2368}
      rintro ⟨hx_pos, hx_div⟩
      have h2 : x ≤ 2368 := by 
        by_contra h
        push_neg at h
        have h3 : 2368 % x = 2368 := by
          rw [Nat.mod_eq_of_lt]
          all_goals linarith
        omega
      interval_cases x <;> norm_num at hx_pos hx_div ⊢
      <;> tauto
    · -- Assume x ∈ {1, 2, 4, 8, 16, 32, 64, 37, 74, 148, 296, 592, 1184, 2368}, prove x ∈ {x | x > 0 ∧ 2368 % x = 0}
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      all_goals
        constructor <;> norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> try { native_decide }