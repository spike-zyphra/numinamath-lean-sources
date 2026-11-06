import Mathlib

theorem algebra_10231 : {a : ℤ | 0 < a ∧ ∃ x : ℤ, a*x^2+2*(2*a-1)*x+4*(a-3) = 0} = {1, 3, 6, 10} := by
  ext a
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · -- Forward direction: if a is a positive integer and there exists integer x such that a*x^2 + 2*(2*a-1)*x + 4*(a-3) = 0, then a ∈ {1, 3, 6, 10}
    intro h
    rcases h with ⟨ha_pos, ⟨x, hx⟩⟩
    have h_eq : a * x^2 + 2 * (2 * a - 1) * x + 4 * (a - 3) = 0 := by
      linarith
    have h_eq2 : a * (x + 2)^2 = 2 * (x + 6) := by
      nlinarith [h_eq]
    have h2 : x + 6 > 0 := by
      nlinarith [show 0 < a from by linarith, sq_nonneg (x + 2), sq_pos_of_ne_zero (show x + 2 ≠ 0 by
        by_contra h
        rw [h] at h_eq2
        nlinarith)]
    have h3 : x ≥ -5 := by omega
    have h4 : x ≤ 20 := by
      by_contra h
      push_neg at h
      nlinarith [show 0 < a from by linarith, sq_nonneg (x + 2), sq_pos_of_ne_zero (show x + 2 ≠ 0 by
        by_contra h
        rw [h] at h_eq2
        nlinarith)]
    interval_cases x <;> omega
  · -- Backward direction: if a ∈ {1, 3, 6, 10}, then there exists integer x such that a*x^2 + 2*(2*a-1)*x + 4*(a-3) = 0
    rintro (rfl | rfl | rfl | rfl)
    · -- a = 1
      constructor
      · norm_num
      · use -4
        norm_num
    · -- a = 3
      constructor
      · norm_num
      · use 0
        norm_num
    · -- a = 6
      constructor
      · norm_num
      · use -3
        norm_num
    · -- a = 10
      constructor
      · norm_num
      · use -1
        norm_num