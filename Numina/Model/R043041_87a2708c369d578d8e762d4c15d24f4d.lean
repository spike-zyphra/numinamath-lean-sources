import Mathlib

theorem algebra_22497 : {x : ℝ | 4 - 7*x ≠ 0 ∧ x^3 + 2 ≠ 0 ∧ (x * (x^2 - 56)) / (4 - 7*x) - (21*x + 22) / (x^3 + 2) = 4} = {-4, -3, -1, 1, 2, 5} := by 
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Forward direction: if x is a solution, prove x ∈ {-4, -3, -1, 1, 2, 5}
    intro h 
    rcases h with ⟨h1, h2, heq⟩
    have heq2 : x * (x^2 - 56) * (x^3 + 2) - (21 * x + 22) * (4 - 7 * x) = 4 * (4 - 7 * x) * (x^3 + 2) := by
      have eq2 : (x * (x^2 - 56)) / (4 - 7 * x) - (21 * x + 22) / (x^3 + 2) =
          (x * (x^2 - 56) * (x^3 + 2) - (21 * x + 22) * (4 - 7 * x)) / ((4 - 7 * x) * (x^3 + 2)) := by 
        field_simp [h1, h2]
        <;> ring
      rw [eq2] at heq
      have eq3 : (x * (x^2 - 56) * (x^3 + 2) - (21 * x + 22) * (4 - 7 * x)) / ((4 - 7 * x) * (x^3 + 2)) = 4 := by 
        linarith 
      have eq4 : (x * (x^2 - 56) * (x^3 + 2) - (21 * x + 22) * (4 - 7 * x)) = 4 * ((4 - 7 * x) * (x^3 + 2)) := by 
        have hd : (4 - 7 * x) * (x^3 + 2) ≠ 0 := by
          apply mul_ne_zero 
          exact h1 
          exact h2 
        field_simp [hd] at eq3 ⊢
        linarith 
      linarith
    have heq5 : (x + 4) * (x + 3) * (x + 1) * (x - 1) * (x - 2) * (x - 5) = 0 := by 
      nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x * (x ^ 2 ) ), sq_nonneg ((x + 4 ) ), sq_nonneg ((x + 3 ) ), sq_nonneg ((x + 1 ) ), sq_nonneg ((x - 1 ) ), sq_nonneg ((x - 2 ) ), sq_nonneg ((x - 5 ) ) ]
    cases' mul_eq_zero.mp heq5 with heq6 heq7
    cases' mul_eq_zero.mp heq6 with heq6 heq7
    cases' mul_eq_zero.mp heq6 with heq6 heq7
    cases' mul_eq_zero.mp heq6 with heq6 heq7
    cases' mul_eq_zero.mp heq6 with heq6 heq7
    · -- Case x + 4 = 0, so x = -4
      have hx : x = -4 := by linarith 
      simp [hx]
    · -- Case x + 3 = 0, so x = -3
      have hx : x = -3 := by linarith 
      simp [hx]
    · -- Case x + 1 = 0, so x = -1
      have hx : x = -1 := by linarith 
      simp [hx]
    · -- Case x - 1 = 0, so x = 1
      have hx : x = 1 := by linarith 
      simp [hx]
    · -- Case x - 2 = 0, so x = 2
      have hx : x = 2 := by linarith 
      simp [hx]
    · -- Case x - 5 = 0, so x = 5
      have hx : x = 5 := by linarith 
      simp [hx]
  · -- Backward direction: if x ∈ {-4, -3, -1, 1, 2, 5}, then x is a solution
    rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals 
      constructor
      · norm_num 
      constructor 
      · norm_num 
      · norm_num