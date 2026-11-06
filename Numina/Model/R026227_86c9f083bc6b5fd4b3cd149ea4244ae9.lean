import Mathlib

theorem number_theory_2842 : {(x, y, z) : ℕ × ℕ × ℕ | 3 * x ^ 3 + 9 * y ^ 3 + 2005 * z ^ 3 = 0} = {(0, 0, 0)} := by
  ext ⟨x, y, z⟩
  simp
  constructor
  · -- Forward implication: Equation implies variables zero
    rintro h
    have eq1 : x = 0 := by
      nlinarith [sq_nonneg (x ^ 2), sq_nonneg (y ^ 2), sq_nonneg (z ^ 2), sq_nonneg (x), sq_nonneg (y), sq_nonneg (z)]
    have eq2 : y = 0 := by
      nlinarith [h, sq_nonneg (x ^ 2), sq_nonneg (y ^ 2), sq_nonneg (z ^ 2), sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), eq1]
    have eq3 : z = 0 := by
      nlinarith [h, sq_nonneg (x ^ 2), sq_nonneg (y ^ 2), sq_nonneg (z ^ 2), sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), eq1, eq2]
    exact ⟨eq1, eq2, eq3⟩
  · -- Backward implication: Variables zero implies equation
    rintro h
    rcases h with ⟨rfl, rfl, rfl⟩
    all_goals norm_num