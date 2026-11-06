import Mathlib

theorem algebra_323196 : Set.ncard {x : ℤ | ⌊(3 * x + 7) / 7⌋ = 4} = 3 := by
  have h1 : {x : ℤ | ⌊(3 * x + 7) / 7⌋ = 4} = {7, 8, 9} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume that floor((3x + 7)/7) = 4. Show that x ∈ {7,8,9}
      intro h
      have h2 : 4 ≤ (3 * x + 7) / 7 := by
        norm_num at h ⊢
        omega
      have h3 : (3 * x + 7) / 7 < 5 := by
        norm_num at h ⊢
        omega
      have h4 : 28 ≤ 3 * x + 7 := by
        omega
      have h5 : 3 * x + 7 < 35 := by
        omega
      have h7 : x ≥ 7 := by
        omega
      have h8 : x ≤ 9 := by
        omega
      interval_cases x <;> norm_num at h ⊢ <;> omega
    · -- Assume x ∈ {7,8,9}. Show that floor((3x + 7)/7) = 4
      rintro (rfl | rfl | rfl)
      · norm_num
      · norm_num
      · norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { native_decide }