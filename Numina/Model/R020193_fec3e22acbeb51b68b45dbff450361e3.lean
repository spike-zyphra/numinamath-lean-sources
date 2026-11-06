import Mathlib

theorem inequalities_326555 : {x : ℤ | x^4 - 51 * x^2 + 50 < 0}.encard = 12 := by
  have h1 : {x : ℤ | x^4 - 51 * x^2 + 50 < 0} = {-7, -6, -5, -4, -3, -2, 2, 3, 4, 5, 6, 7} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume x^4 - 51 * x^2 + 50 < 0, need to prove x ∈ {-7, -6, -5, -4, -3, -2, 2, 3, 4, 5, 6, 7}
      intro h
      have h2 : x^4 - 51 * x^2 + 50 = (x^2 - 1) * (x^2 - 50) := by ring
      rw [h2] at h
      have h3 : (x^2 - 1) * (x^2 - 50) < 0 := h
      cases mul_neg_iff.mp h with
      | inl h4 =>
        have h5 : x^2 > 1 := by linarith
        have h6 : x^2 < 50 := by linarith
        have h7 : x ≤ 7 := by nlinarith
        have h8 : x ≥ -7 := by nlinarith
        interval_cases x <;> norm_num at h5 h6 ⊢ <;> tauto
      | inr h4 =>
        have h5 : x^2 < 1 := by linarith
        have h6 : x^2 > 50 := by linarith
        nlinarith
    · -- Assume x ∈ {-7, -6, -5, -4, -3, -2, 2, 3, 4, 5, 6, 7}, need to prove x^4 - 51 * x^2 + 50 < 0
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      all_goals
        norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> try { native_decide }