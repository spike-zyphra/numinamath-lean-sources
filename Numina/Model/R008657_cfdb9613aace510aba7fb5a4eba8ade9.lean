import Mathlib

theorem algebra_11974 : {x : ℤ | abs (5 * x - 3) ≤ 7}.encard = 3 := by 
  have h1 : {x : ℤ | abs (5 * x - 3) ≤ 7} = {0, 1, 2} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, 
      Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume abs (5 * x - 3) ≤ 7, prove x ∈ {0, 1, 2}
      intro h
      have h1 : -7 ≤ 5 * x - 3 := by 
        linarith [abs_le.mp h]
      have h2 : 5 * x - 3 ≤ 7 := by 
        linarith [abs_le.mp h]
      omega
    · -- Assume x ∈ {0, 1, 2}, prove abs (5 * x - 3) ≤ 7
      rintro (rfl | rfl | rfl)
      · -- x = 0
        norm_num
      · -- x = 1
        norm_num
      · -- x = 2
        norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard]
  <;> rfl