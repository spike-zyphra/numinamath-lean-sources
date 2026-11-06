import Mathlib

theorem algebra_10273 : {x : ℝ | x ^ 2 + 5 * x < 6} = Set.Ioo (-6) 1 := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_Ioo]
  constructor
  · -- Forward direction: If x^2 + 5x < 6, then -6 < x < 1
    intro h
    constructor
    · -- Show -6 < x
      nlinarith [sq_nonneg (x + 6 / 2), sq_nonneg (x - 1 / 2), sq_nonneg (x + 6), sq_nonneg (x - 1)]
    · -- Show x < 1
      nlinarith [sq_nonneg (x + 6 / 2), sq_nonneg (x - 1 / 2), sq_nonneg (x + 6), sq_nonneg (x - 1)]
  · -- Backward direction: If -6 < x < 1, then x^2 + 5x < 6
    rintro ⟨h1, h2⟩
    nlinarith [sq_nonneg (x + 6 / 2), sq_nonneg (x - 1 / 2), sq_nonneg (x + 6), sq_nonneg (x - 1)]