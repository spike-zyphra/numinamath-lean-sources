import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_315458 (f : ℝ → ℝ) (hf : f = λ x => (x + 1)^3 * (x^3 + 5 * x)) :
    {x | f x < 10 * (x + 1)^2 + 8} = {x | -2 < x ∧ x < 1} := by
  ext x
  simp [hf]
  constructor
  · -- Assume (x + 1)^3 * (x ^ 3 + 5 * x) < 10 * (x + 1) ^ 2 + 8, prove -2 < x ∧ x < 1
    intro h
    have h1 : -2 < x := by
      nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (x + 2), sq_nonneg (x - 1), sq_nonneg (x ^ 2 + x), sq_nonneg (x + 1), sq_nonneg (x), sq_nonneg (x ^ 2 - x), sq_nonneg (x * (x - 1)), sq_nonneg ((x + 2) * (x - 1)), sq_nonneg ((x + 1) * x), sq_nonneg ((x + 2) * (x + 1)), sq_nonneg ((x - 1) * x)]
    have h2 : x < 1 := by
      nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (x + 2), sq_nonneg (x - 1), sq_nonneg (x ^ 2 + x), sq_nonneg (x + 1), sq_nonneg (x), sq_nonneg (x ^ 2 - x), sq_nonneg (x * (x - 1)), sq_nonneg ((x + 2) * (x - 1)), sq_nonneg ((x + 1) * x), sq_nonneg ((x + 2) * (x + 1)), sq_nonneg ((x - 1) * x)]
    constructor
    · linarith
    · linarith
  · -- Assume -2 < x ∧ x < 1, prove (x + 1) ^ 3 * (x ^ 3 + 5 * x) < 10 * (x + 1) ^ 2 + 8
    rintro ⟨h1, h2⟩
    nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (x + 2), sq_nonneg (x - 1), sq_nonneg (x ^ 2 + x), sq_nonneg (x + 1), sq_nonneg (x), sq_nonneg (x ^ 2 - x), sq_nonneg (x * (x - 1)), sq_nonneg ((x + 2) * (x - 1)), sq_nonneg ((x + 1) * x), sq_nonneg ((x + 2) * (x + 1)), sq_nonneg ((x - 1) * x), mul_pos (sub_pos.mpr (show (-2 : ℝ) < x by linarith)) (sub_pos.mpr (show (x : ℝ) < (1 : ℝ) by linarith)), mul_pos (sub_pos.mpr (show (x : ℝ) < (1 : ℝ) by linarith)) (show (0 : ℝ) < (1 : ℝ) by linarith)]