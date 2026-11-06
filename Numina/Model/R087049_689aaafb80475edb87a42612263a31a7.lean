import Mathlib
open Real Int Nat Set
open scoped BigOperators

theorem inequalities_9577 : {x : ℤ | 11 * x + 42 > x ^ 2}.encard = 16 := by
  have h1 : {x : ℤ | 11 * x + 42 > x ^ 2} = Set.Icc (-2) 13 := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · -- Assume 11*x + 42 > x^2, prove -2 <= x ∧ x <= 13
      intro h
      constructor
      · -- Prove -2 <= x
        nlinarith [sq_nonneg (x), sq_nonneg (x + 2)]
      · -- Prove x <= 13
        nlinarith [sq_nonneg (x), sq_nonneg (x - 13)]
    · -- Assume -2 <= x ∧ x <= 13, prove 11*x + 42 > x^2
      rintro ⟨h1, h2⟩
      nlinarith [sq_nonneg (x), sq_nonneg (x + 2), sq_nonneg (x - 13)]
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_eq_toFinset_card']
  <;> rfl