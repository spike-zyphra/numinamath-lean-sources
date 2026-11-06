import Mathlib

open Real
open scoped BigOperators

theorem inequalities_3885 :
  ∑ᶠ x ∈ {x : ℤ | x^2 - 4*x - abs (5*x - 12) + 6 < 0}, x = -2 - 1 + 0 + 1 + 4 + 5 := by 
  have h1 : {x : ℤ | x^2 - 4*x - abs (5*x - 12) + 6 < 0} = {-2, -1, 0, 1, 4, 5} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume x^2 - 4*x - abs (5*x - 12) + 6 < 0, prove x ∈ {-2, -1, 0, 1, 4, 5}
      intro h
      have h2 : x^2 - 4*x - abs (5*x - 12) + 6 < 0 := h
      by_cases h3 : 5*x - 12 ≥ 0
      · -- Case where 5*x - 12 ≥ 0 (so abs(5*x - 12) = 5*x - 12)
        rw [abs_of_nonneg h3] at h2
        have h4 : x > 3 := by nlinarith
        have h5 : x < 6 := by nlinarith
        interval_cases x <;> norm_num at h2 ⊢ <;> tauto
      · -- Case where 5*x - 12 < 0 (so abs(5*x - 12) = 12 - 5*x)
        have h4 : 5*x - 12 < 0 := by linarith
        rw [abs_of_neg h4] at h2
        have h5 : x > -3 := by nlinarith
        have h6 : x < 2 := by nlinarith
        interval_cases x <;> norm_num at h2 ⊢ <;> tauto
    · -- Assume x ∈ {-2, -1, 0, 1, 4, 5}, prove x^2 - 4*x - abs (5*x - 12) + 6 < 0
      rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      · -- Case x = -2
        norm_num
      · -- Case x = -1
        norm_num
      · -- Case x = 0
        norm_num
      · -- Case x = 1
        norm_num
      · -- Case x = 4
        norm_num
      · -- Case x = 5
        norm_num
  rw [h1]
  rw [finsum_mem_eq_toFinset_sum]
  simp [Set.mem_insert_iff, Set.mem_singleton_iff]
  <;> rfl
  <;> try { tauto }
  <;> try { linarith }