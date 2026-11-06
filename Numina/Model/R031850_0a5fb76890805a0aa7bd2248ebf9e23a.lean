import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_16170 (f : ℝ → ℝ) (hf : f = λ x => x / (x ^ 2 - x + 1)) :
  range f = {y | -1/3 ≤ y ∧ y ≤ 1} := by
  ext y
  simp [hf, Set.mem_range]
  constructor
  · -- Assume y is in the range, prove -1/3 ≤ y ∧ y ≤ 1
    rintro ⟨x, hx⟩
    have h1 : x ^ 2 - x + 1 > 0 := by
      nlinarith [sq_nonneg (x - 1 / 2)]
    have h3 : x = y * (x ^ 2 - x + 1) := by
      field_simp [(show x ^ 2 - x + 1 ≠ 0 by nlinarith [sq_nonneg (x - 1 / 2)])] at hx ⊢
      linarith
    have h4 : y * (x ^ 2 ) - (y + 1) * x + y = 0 := by
      nlinarith [h3]
    have h4' : (y + 1) ^ 2 - 4 * y * y ≥ 0 := by
      nlinarith [sq_nonneg (y * x - (y + 1) / 2), sq_nonneg (y), sq_nonneg (y * x), sq_nonneg (x - (y + 1) / (2 * y)), sq_nonneg (y - 1), sq_nonneg (y + 1 / 3)]
    have h6 : -1/3 ≤ y := by
      nlinarith [sq_nonneg (y - 1), sq_nonneg (y + 1 / 3)]
    have h7 : y ≤ 1 := by
      nlinarith [sq_nonneg (y - 1), sq_nonneg (y + 1 / 3)]
    exact ⟨h6, h7⟩
  · -- Assume -1/3 ≤ y ∧ y ≤ 1, prove y is in the range
    rintro ⟨hy1, hy2⟩
    by_cases heq : y = 0
    · -- When y = 0, choose x = 0
      use 0
      simp [heq]
    · -- When y ≠ 0, we need to solve the quadratic.
      have h4' : y ≠ 0 := by
        intro h
        apply heq
        linarith
      have h8 : ∃ x : ℝ, y * x ^ 2 - (y + 1) * x + y = 0 := by
        have h4 : (y + 1) ^ 2 - 4 * y * y ≥ 0 := by
          nlinarith [sq_nonneg (y - 1), sq_nonneg (y + 1 / 3)]
        use ((y + 1) + Real.sqrt ((y + 1) ^ 2 - 4 * y ^ 2)) / (2 * y)
        field_simp [h4']
        ring_nf
        rw [Real.sq_sqrt (by nlinarith)]
        <;> nlinarith
      rcases h8 with ⟨x, heq⟩
      use x
      field_simp [(show x ^ 2 - x + 1 ≠ 0 by
        nlinarith [sq_nonneg (x - 1 / 2)]
      )] at *
      nlinarith [heq, sq_nonneg (x - (y + 1) / (2 * y)), sq_nonneg (y), sq_nonneg (x), sq_nonneg (y + 1 / 3)]