import Mathlib

theorem algebra_19794 : {x : ℤ | abs (x - 2) ≤ 56 / 10}.encard = 11 := by
  have h1 : {x : ℤ | abs (x - 2) ≤ 56 / 10} = {-3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7} := by 
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume abs (x - 2) ≤ 56 / 10
      intro h
      norm_num at h 
      have h2 : abs (x - 2) ≤ 5 := by 
        omega 
      have h3 : -5 ≤ x - 2 := by 
        linarith [abs_le.mp h2]
      have h4 : x - 2 ≤ 5 := by 
        linarith [abs_le.mp h2]
      have h5 : -3 ≤ x := by 
        omega
      have h6 : x ≤ 7 := by 
        omega 
      omega 
    · -- Assume x ∈ {-3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7}
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      all_goals 
        norm_num 
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard]
  <;> try { aesop }