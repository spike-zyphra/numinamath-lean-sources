import Mathlib

open Set Real

theorem inequalities_160568 {A B : Set ℝ}
    (hA : A = {x | x + 1 ≥ 0}) (hB : B = {x | x^2 - 2 ≥ 0}) :
    A ∩ (Set.univ \ B) = {x | -1 ≤ x ∧ x < sqrt 2} := by 
  ext x
  simp [hA, hB, Set.mem_inter, Set.mem_setOf_eq, Set.mem_diff]
  constructor
  · -- Assume (x + 1 ≥ 0) ∧ (x ^ 2 - 2 < 0), prove (-1 ≤ x ∧ x < sqrt 2).
    intro h
    rcases h with ⟨hx1, hx2⟩
    constructor
    · -- Show -1 ≤ x
      nlinarith
    · -- Show x < sqrt 2
      nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · -- Assume (-1 ≤ x ∧ x < sqrt 2), prove (x + 1 ≥ 0) ∧ (x ^ 2 - 2 < 0).
    rintro ⟨hx1, hx2⟩
    constructor
    · -- Show x + 1 ≥ 0
      linarith
    · -- Show x ^ 2 - 2 < 0
      have h4 : x ^ 2 < (2 : ℝ) := by
        have h11 : -1 ≤ x := hx1
        have h12 : x < Real.sqrt 2 := hx2
        by_cases h : x ≥ 0
        · -- If x ≥ 0, then x < sqrt 2 implies x^2 < 2.
          nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
        · -- If x < 0. But since x ≥ -1, we have -1 ≤ x < 0. In this case, x^2 < 1, so x^2 < 2.
          nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), sq_nonneg (x), mul_nonneg (show (0 : ℝ) ≤ (x + 1) by linarith) (show (0 : ℝ) ≤ (1 : ℝ) by norm_num)]
      nlinarith