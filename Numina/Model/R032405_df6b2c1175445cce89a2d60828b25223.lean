import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_117462 (f : ℝ → ℝ) (hf : f = λ x => (x^2 - x + 1)/(x^2 + x + 1)) :
    range f = {y | 1/3 ≤ y ∧ y ≤ 3} := by
  ext y
  simp [hf, mem_range]
  constructor
  · -- Assume y ∈ range f
    rintro ⟨x, hx⟩
    have h1 : (x ^ 2 - x + 1) / (x ^ 2 + x + 1) = y := by
      simpa using hx
    have h2 : x^2 + x + 1 > 0 := by
      nlinarith [sq_nonneg (x + 1/2)]
    have h3 : (x ^ 2 - x + 1) = y * (x ^ 2 + x + 1) := by
      have hne : x^2 + x + 1 ≠ 0 := by
        by_contra h
        have : x^2 + x + 1 = 0 := by linarith
        nlinarith [sq_nonneg (x + 1/2)]
      field_simp [hne] at h1 ⊢
      linarith
    have h4 : -3 * y^2 + 10 * y - 3 ≥ 0 := by
      nlinarith [sq_nonneg (x * (1 - y) + (-1 - y) / 2), sq_nonneg ((x) + 1 / 2), sq_nonneg (y - 3), sq_nonneg (y - 1 / 3), sq_nonneg ((x^2 + x + 1) * (y - 1 / 3)), sq_nonneg ((x^2 + x + 1) * (y - 3)), sq_nonneg ((x^2 + x + 1) * (1 - y)), sq_nonneg ((x + (1 / 2)) * (1 - y))]
    constructor
    · -- Prove 1/3 ≤ y
      nlinarith
    · -- Prove y ≤ 3
      nlinarith
  · -- Assume 1/3 ≤ y ∧ y ≤ 3
    rintro ⟨hy1, hy2⟩
    by_cases h3 : 1 - y = 0
    · -- If 1 - y = 0 (i.e., y = 1), the equation is trivial.
      have : y = 1 := by linarith
      use (0)
      rw [this]
      norm_num
    · -- If 1 - y ≠ 0, can solve quadratic
      have h4 : 1 - y ≠ 0 := by
        intro h
        apply h3
        linarith
      have h1 : -3 * y^2 + 10 * y - 3 ≥ 0 := by
        nlinarith
      have h5 : ∃ x, (1 - y) * x ^ 2 + (-1 - y) * x + (1 - y) = 0 := by
        use ( (1 + y) + Real.sqrt (-3 * y^2 + 10 * y - 3) ) / (2 * (1 - y))
        field_simp [h4]
        ring_nf
        rw [Real.sq_sqrt (by nlinarith)]
        <;> nlinarith
      rcases h5 with ⟨x, hx_eq⟩
      use x
      have h2x : x ^ 2 + x + 1 > 0 := by
        nlinarith [sq_nonneg (x + 1 / 2)]
      have h3 : (x ^ 2 - x + 1) = y * (x ^ 2 + x + 1) := by
        have h4 : (1 - y) * x ^ 2 + (-1 - y) * x + (1 - y) = 0 := hx_eq
        nlinarith
      field_simp [h2x]
      linarith