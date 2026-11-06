import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_300157 : range (λ x => (x^2 + 2 * x + 3) / (x^2 + 4 * x + 5)) =
  {y | 2 - sqrt 2 ≤ y ∧ y ≤ 2 + sqrt 2} := by
  ext y
  simp only [mem_range, mem_setOf_eq]
  constructor
  · -- First, show that if y is in the range, then it's in the interval
    intro hy
    rcases hy with ⟨x, hx⟩
    have h1 : x^2 + 4 * x + 5 > 0 := by
      nlinarith [sq_nonneg (x + 2)]
    have eq1 : (x^2 + 2 * x + 3) = y * (x^2 + 4 * x + 5) := by
      field_simp [(show x^2 + 4 * x + 5 ≠ 0 by
        by_contra h
        have : x^2 + 4 * x + 5 = 0 := by linarith
        nlinarith [sq_nonneg (x + 2)]
      )] at hx ⊢
      linarith [hx]
    have h2 : (y - 1) * x^2 + (4 * y - 2) * x + (5 * y - 3) = 0 := by
      nlinarith [eq1]
    have h3 : (4 * y - 2)^2 - 4 * (y - 1) * (5 * y - 3) ≥ 0 := by
      nlinarith [sq_nonneg ((y - 1) * x + (4 * y - 2)/2), sq_nonneg (x * (y - 1) + (4 * y - 2) / 2), sq_nonneg (x + 2), sq_nonneg (y - 2), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have h4 : y ^ 2 - 4 * y + 2 ≤ 0 := by
      nlinarith
    constructor
    · -- Show 2 - sqrt 2 ≤ y
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    · -- Show y ≤ 2 + sqrt 2
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  · -- Now the reverse direction: if y is in the interval, it's in the range
    rintro ⟨hy1, hy2⟩
    by_cases h : y - 1 = 0
    · -- y - 1 = 0, so y = 1
      have hy11 : y = 1 := by 
        linarith
      use -1
      rw [hy11]
      norm_num
    · -- y - 1 ≠ 0
      have h5 : y - 1 ≠ 0 := by
        intro h6
        apply h
        linarith
      have h4 : (4 * y - 2)^2 - 4 * (y - 1) * (5 * y - 3) ≥ 0 := by
        have h3 : y ^ 2 - 4 * y + 2 ≤ 0 := by 
          nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (y - 2), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]
        nlinarith
      have h6 : ∃ x, (y - 1) * x^2 + (4 * y - 2) * x + (5 * y - 3) = 0 := by
        have h7 : (4 * y - 2) ^ 2 - 4 * (y - 1) * (5 * y - 3) ≥ 0 := h4
        use ( - (4 * y - 2) - Real.sqrt ((4 * y - 2) ^ 2 - 4 * (y - 1) * (5 * y - 3)) ) / (2 * (y - 1))
        field_simp [h5]
        ring_nf 
        rw [Real.sq_sqrt (by linarith)]
        <;> nlinarith
      rcases h6 with ⟨x, hx⟩
      use x
      have h11 : x^2 + 4 * x + 5 > 0 := by
        nlinarith [sq_nonneg (x + 2)]
      have eq1 : (x^2 + 2 * x + 3) = y * (x^2 + 4 * x + 5) := by 
        have h2 : (y - 1) * x^2 + (4 * y - 2) * x + (5 * y - 3) = 0 := hx
        nlinarith [h2]
      field_simp [ne_of_gt h11]
      linarith [eq1]