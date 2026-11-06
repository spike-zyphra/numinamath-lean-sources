import Mathlib

theorem number_theory_231017 :
    {n : ℕ | 1000 ≤ n ∧ n ≤ 4000 ∧ n % 11 = 2 ∧ n % 13 = 12 ∧ n % 19 = 18} = {1234, 3951} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Assume n in left side, prove it's in the right side
    rintro ⟨h1, h2, h3, h4, h5⟩
    have h6 : n ≥ 1000 := by linarith
    have h7 : n ≤ 4000 := by linarith
    interval_cases n <;> norm_num at h3 h4 h5 ⊢ <;> omega
  · -- Assume n in right side, prove it's in the left side
    rintro (rfl | rfl)
    · -- n = 1234
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- n = 3951
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num