import Mathlib

theorem algebra_2845 : {x : ℤ | ⌊(3 * x + 7) / 7⌋ = 4}.encard = 3 := by
  have h1 : {x : ℤ | ⌊(3 * x + 7) / 7⌋ = 4} = {7, 8, 9} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume ⌊(3 * x + 7) / 7⌋ = 4, prove x ∈ {7, 8, 9}
      intro h
      have h2 : 4 ≤ (3 * x + 7) / 7 := by
        norm_num at h ⊢
        omega
      have h3 : (3 * x + 7) / 7 < 5 := by
        norm_num at h ⊢
        omega
      have h4 : 7 ≤ x := by
        omega
      have h5 : x ≤ 9 := by
        omega
      interval_cases x <;> try { tauto }
    · -- Assume x ∈ {7, 8, 9}, prove ⌊(3 * x + 7) / 7⌋ = 4
      rintro (rfl | rfl | rfl)
      · norm_num
      · norm_num
      · norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard]
  <;> try native_decide