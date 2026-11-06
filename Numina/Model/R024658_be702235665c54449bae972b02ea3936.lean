import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_125963 : {x | ∃ a b : ℝ, x = a^2 + (a*b + 1)^2} = {x | 0 < x} := by
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · -- Assume $x = a^2 + (a \cdot b + 1)^2$ for some $a, b$, prove $0 < x$
    rintro ⟨a, b, h_eq⟩
    have h1 : a ^ 2 ≥ 0 := sq_nonneg a
    have h2 : (a * b + 1) ^ 2 ≥ 0 := sq_nonneg (a * b + 1)
    have h3 : a ^ 2 + (a * b + 1) ^ 2 > 0 := by
      by_contra h
      push_neg at h
      have h4 : a ^ 2 = 0 := by
        nlinarith [sq_nonneg (a * b + 1), sq_nonneg a]
      have h5 : a * b + 1 = 0 := by
        nlinarith [sq_nonneg (a * b + 1), sq_nonneg a]
      have h6 : a = 0 := by
        nlinarith
      rw [h6] at h5
      nlinarith
    nlinarith
  · -- Assume $0 < x$, prove $\exists a b, x = a^2 + (a \cdot b + 1)^2$
    intro h
    use Real.sqrt x, -1 / Real.sqrt x
    have h1 : Real.sqrt x > 0 := by
      apply Real.sqrt_pos.mpr
      linarith
    have h2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by nlinarith)
    have h3 : (Real.sqrt x : ℝ) * (-1 / Real.sqrt x) = -1 := by
      field_simp [h1]
      <;> linarith
    nlinarith [Real.sqrt_nonneg x, sq_nonneg (Real.sqrt x * (-1 / Real.sqrt x) + 1), Real.sq_sqrt (show (0 : ℝ) ≤ x by nlinarith), sq_pos_of_pos h1]