import Mathlib

theorem number_theory_259779 :
  {n : ℕ | n ≤ 100000 / 5 ∧ n % 12 = 3 ∧ n % 18 = 3 ∧ n % 45 = 3 ∧ n % 11 = 0} =
  {363, 2343, 4323, 6303, 8283, 10263, 12243, 14223, 16203, 18183} := by 
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Forward implication: show that if n satisfies the conditions, it must be one of the 10 values
    intro h
    rcases h with ⟨h1, h2, h3, h4, h5⟩
    have h1' : n ≤ 20000 := by 
      omega 
    have h6 : n % 180 = 3 := by 
      have h1 : n % 12 = 3 := h2
      have h2 : n % 18 = 3 := h3
      have h3 : n % 45 = 3 := h4
      omega 
    have h7 : n % 1980 = 363 := by 
      omega 
    have h8 : n = 363 ∨ n = 2343 ∨ n = 4323 ∨ n = 6303 ∨ n = 8283 ∨ n = 10263 ∨ n = 12243 ∨ n = 14223 ∨ n = 16203 ∨ n = 18183 := by 
      omega 
    tauto 
  · -- Backward implication: show that each of the 10 values satisfies the conditions
    intro h 
    rcases h with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · -- n = 363 
      constructor 
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- n = 2343 
      constructor 
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- n = 4323 
      constructor 
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- n = 6303 
      constructor 
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- n = 8283 
      constructor 
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- n = 10263 
      constructor 
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- n = 12243 
      constructor 
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- n = 14223 
      constructor 
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- n = 16203 
      constructor 
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- n = 18183 
      constructor 
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num