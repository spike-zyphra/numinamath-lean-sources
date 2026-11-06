import Mathlib

theorem algebra_15338 : {x : ℤ | ¬(5 * x ^ 2 + 19 * x + 16 > 20)}.encard = 5 := by
  have h1 : {x : ℤ | ¬(5 * x ^ 2 + 19 * x + 16 > 20)} = {-4, -3, -2, -1, 0} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Show that if ¬(5 * x ^ 2 + 19 * x + 16 > 20), then x in {-4, -3, -2, -1, 0}
      intro h
      have h2 : 5 * x ^ 2 + 19 * x + 16 ≤ 20 := by linarith
      have h3 : 5 * x ^ 2 + 19 * x - 4 ≤ 0 := by linarith
      have h4 : x ≥ -4 := by nlinarith [sq_nonneg (5 * x + 20), sq_nonneg (x + 4)]
      have h5 : x ≤ 0 := by nlinarith [sq_nonneg (5 * x + 1), sq_nonneg (x - 0)]
      interval_cases x <;> norm_num at h3 ⊢
      <;> tauto
    · -- Show that if x in {-4, -3, -2, -1, 0}, then ¬(5 * x ^ 2 + 19 * x + 16 > 20)
      rintro (rfl | rfl | rfl | rfl | rfl)
      · -- x = -4
        norm_num
      · -- x = -3
        norm_num
      · -- x = -2
        norm_num
      · -- x = -1
        norm_num
      · -- x = 0
        norm_num
  rw [h1]
  rw [Set.encard]
  simp