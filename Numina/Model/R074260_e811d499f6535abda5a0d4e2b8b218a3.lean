import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_299841 {S : ℝ → ℝ} (hS : S = λ x => abs (x - 2) + abs (x - 4)) :
    IsLeast (range S) 2 ∧ ∀ m, (∀ x y, S x ≥ m * (-y^2 + 2 * y)) → m ≤ 2 := by
  constructor
  · -- Show 2 is the least element in the range of S, so 2 is the minimum value
    constructor
    · -- Show 2 is attained, so is in the range
      use 3
      simp [hS]
      all_goals norm_num
    · -- Show no value less than 2 is attained
      intro k
      rintro ⟨x, hx⟩
      simp [hS] at hx
      have h1 : abs (x - 2) + abs (x - 4) ≥ 2 := by
        cases abs_cases (x - 2) with
        | inl h1 =>
          cases abs_cases (x - 4) with
          | inl h2 =>
            linarith
          | inr h2 =>
            linarith
        | inr h1 =>
          cases abs_cases (x - 4) with
          | inl h2 =>
            linarith
          | inr h2 =>
            linarith
      linarith
  · -- Show if ∀ x, y, S x ≥ m * (-y^2 + 2 * y) then m ≤ 2
    intro m
    intro h
    -- Choose x = 3 (where S 3 = 2) and y = 1 (which maximizes -y² + 2y to 1).
    -- This gives 2 ≥ m * 1, hence m ≤ 2.
    have h1 := h 3 1
    have h2 : S 3 = 2 := by
      simp [hS]
      all_goals norm_num
    have h3 : - (1 : ℝ) ^ 2 + 2 * (1 : ℝ) = 1 := by norm_num
    -- Simplify S 3 and compute -y² + 2y at y = 1
    rw [show S 3 = 2 by linarith [h2], show - (1 : ℝ) ^ 2 + 2 * (1 : ℝ) = 1 by linarith [h3] ] at h1
    nlinarith