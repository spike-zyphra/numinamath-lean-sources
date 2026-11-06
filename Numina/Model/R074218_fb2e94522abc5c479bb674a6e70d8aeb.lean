import Mathlib

theorem algebra_10442 : {x : ℤ | x ^ 2 < 7 * x}.encard = 6 := by 
  have h1 : {x : ℤ | x ^ 2 < 7 * x} = {1, 2, 3, 4, 5, 6} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume x^2 < 7x
      intro h
      have h2 : x > 0 := by
        nlinarith
      have h3 : x < 7 := by
        nlinarith
      interval_cases x <;> tauto
    · -- Show that if x ∈ {1, 2, 3, 4, 5, 6}, then x^2 < 7x
      rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      · -- x = 1
        norm_num
      · -- x = 2
        norm_num
      · -- x = 3
        norm_num
      · -- x = 4
        norm_num
      · -- x = 5
        norm_num
      · -- x = 6
        norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard]
  <;> try { rfl }