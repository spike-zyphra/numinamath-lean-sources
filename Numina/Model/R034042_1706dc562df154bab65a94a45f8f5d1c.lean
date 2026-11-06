import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_328444 {f : ℝ → ℝ} (hf : f = λ x => (x^2 + 3 * x + 1) / (x^2 - x + 1)) :
    range f = {y | -1 / 3 ≤ y ∧ y ≤ 5} := by

  ext y
  simp only [hf, Set.mem_range, Set.mem_setOf_eq]
  constructor
  · -- Assume y ∈ range f, so there exists x s.t. f(x) = y.
    rintro ⟨x, hx⟩
    have h1 : x^2 - x + 1 > 0 := by
      nlinarith [sq_nonneg (x - 1 / 2)]
    have eq1 : (x ^ 2 + 3 * x + 1) = y * (x^2 - x + 1) := by
      have h2 : x ^ 2 - x + 1 ≠ 0 := by
        nlinarith [sq_nonneg (x - 1 / 2)]
      field_simp [h2] at hx
      nlinarith
    have eq2 : (1 - y) * x^2 + (3 + y) * x + (1 - y) = 0 := by
      nlinarith [eq1]

    constructor
    · -- Show that $-1/3 \leq y$
      nlinarith [sq_nonneg ((1 - y) * x + (3 + y) / 2), sq_nonneg (x + 1), sq_nonneg (x - 1 / 2), sq_nonneg ((1 - y) * x + (1)), sq_nonneg ((3 + y) * x + (1 - y)), sq_nonneg ((x + 1 / 2))]
    · -- Show that $y \leq 5$
      nlinarith [sq_nonneg ((1 - y) * x + (3 + y) / 2), sq_nonneg (x + 1), sq_nonneg (x - 1 / 2), sq_nonneg ((1 - y) * x + (1)), sq_nonneg ((3 + y) * x + (1 - y)), sq_nonneg ((x + 1 / 2))]
  · -- Assume $-1/3 \leq y \leq 5$.
    rintro ⟨hy1, hy2⟩
    by_cases h4 : (1 - y) = (0 : ℝ)
    · -- If 1 - y = 0, then y = 1
      have h5 : y = 1 := by nlinarith
      use 0
      rw [h5]
      norm_num
    · -- Case 1 - y ≠ 0.
      have h4' : (1 - y) ≠ 0 := by exact_mod_cast h4
      have eq3 : (3 + y) ^ 2 - 4 * ((1 - y) : ℝ) * ((1 - y) : ℝ) ≥ 0 := by
        nlinarith [sq_nonneg (y - 1), sq_nonneg (y + 1 / 3), sq_nonneg (y - 5)]
      have h3_eq : ∃ x: ℝ, (1 - y) * x ^ 2 + (3 + y) * x + (1 - y) = 0 := by
        have h_eq3 : (3 + y) ^ 2 - 4 * ((1 - y) : ℝ) * ((1 - y) : ℝ) ≥ 0 := by
          nlinarith [sq_nonneg (y - 1), sq_nonneg (y + 1 / 3), sq_nonneg (y - 5)]
        use (- (3 + y) + Real.sqrt ((3 + y) ^ 2 - 4 * ((1 - y) : ℝ) * ((1 - y) : ℝ)) ) / (2 * (1 - y))
        field_simp [(show (1 - y) ≠ 0 by exact_mod_cast h4)]
        ring_nf
        rw [Real.sq_sqrt (by nlinarith)]
        <;> nlinarith
      rcases h3_eq with ⟨x3, h_eq3⟩
      use x3
      have eq2 : (1 - y) * x3^2 + (3 + y) * x3 + (1 - y) = 0 := h_eq3
      have hx3 : x3^2 - x3 + 1 > 0 := by
        nlinarith [sq_nonneg (x3 - 1 / 2)]
      field_simp [hx3]
      nlinarith