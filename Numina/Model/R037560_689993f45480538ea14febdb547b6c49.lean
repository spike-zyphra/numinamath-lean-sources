import Mathlib

theorem algebra_319978 :
    Set.ncard {x : ℤ | ⌊(3 * x + 7) / 7⌋ = 4} = 3 := by
  have h1 : {x : ℤ | ⌊(3 * x + 7) / 7⌋ = 4} = {7, 8, 9} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume that ⌊(3 * x + 7) / 7⌋ = 4, prove that x ∈ {7, 8, 9}
      intro h
      have h4 : 4 ≤ (3 * x + 7) / 7 := by 
        have h3 : ⌊(3 * x + 7) / 7⌋ = 4 := h
        norm_num at h3 ⊢
        omega
      have h5 : (3 * x + 7) / 7 < 5 := by 
        have h4 : ⌊(3 * x + 7) / 7⌋ = 4 := h
        norm_num at h4 ⊢
        omega
      omega
    · -- Assume x ∈ {7, 8, 9}, prove that ⌊(3 * x + 7) / 7⌋ = 4
      rintro (h | h | h)
      · -- x = 7
        rw [h]
        norm_num
      · -- x = 8
        rw [h]
        norm_num
      · -- x = 9
        rw [h]
        norm_num
  rw [h1]
  norm_num [Set.ncard_insert_of_not_mem, Set.ncard_singleton]