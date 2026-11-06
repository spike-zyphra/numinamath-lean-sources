import Mathlib

theorem number_theory_691 : {a : ℕ | 1 ≤ a ∧ a ≤ 1995 ∧ (1995 + a) ∣ 1995 * a} = {1330, 798, 532, 210, 1254, 1680} := by
  ext a
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Forward direction
    rintro ⟨ha1, ha2, h⟩
    interval_cases a <;> norm_num at h ⊢ <;> tauto
  · -- Backward direction
    rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    · -- a = 1330
      constructor
      · norm_num 
      constructor
      · norm_num 
      · norm_num 
    · -- a = 798
      constructor
      · norm_num 
      constructor
      · norm_num 
      · norm_num 
    · -- a = 532
      constructor
      · norm_num 
      constructor
      · norm_num 
      · norm_num 
    · -- a = 210
      constructor
      · norm_num 
      constructor
      · norm_num 
      · norm_num 
    · -- a = 1254
      constructor
      · norm_num 
      constructor
      · norm_num 
      · norm_num 
    · -- a = 1680
      constructor
      · norm_num 
      constructor
      · norm_num 
      · norm_num