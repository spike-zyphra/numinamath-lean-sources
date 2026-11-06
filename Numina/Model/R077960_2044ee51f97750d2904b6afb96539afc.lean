import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_321 : {n : ℤ | ∃ x y, n = x + y ∧ x^2 + y^2 + 1 ≤ 2 * x + 2 * y}.ncard = 3 := by
  have h1 : {n : ℤ | ∃ x y, n = x + y ∧ x^2 + y^2 + 1 ≤ 2 * x + 2 * y} = {1, 2, 3} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume n is in the original set
      intro h
      rcases h with ⟨x, y, h_eq, h_ineq⟩
      have h2 : (x - 1) ^ 2 + (y - 1) ^ 2 ≤ 1 := by
        nlinarith
      have hx1 : x ≥ 0 := by
        nlinarith [sq_nonneg (x - 1 : ℤ), sq_nonneg (y - 1 : ℤ)]
      have hx2 : x ≤ 2 := by
        nlinarith [sq_nonneg (x - 1 : ℤ), sq_nonneg (y - 1 : ℤ)]
      have hy1 : y ≥ 0 := by
        nlinarith [sq_nonneg (x - 1 : ℤ), sq_nonneg (y - 1 : ℤ)]
      have hy2 : y ≤ 2 := by
        nlinarith [sq_nonneg (x - 1 : ℤ), sq_nonneg (y - 1 : ℤ)]
      interval_cases x <;> interval_cases y
      <;> omega
    · -- Show that if n ∈ {1, 2, 3}, then there exist x,y such that n = x + y and x^2+y^2+1 ≤ 2*x+2*y
      rintro (rfl | rfl | rfl)
      · -- n = 1
        use 0, 1
        all_goals norm_num
      · -- n = 2
        use 1, 1
        all_goals norm_num
      · -- n = 3
        use 1, 2
        all_goals norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> native_decide