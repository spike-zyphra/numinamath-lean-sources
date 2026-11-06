import Mathlib

theorem algebra_611093 : 
  ∃ (P : Polynomial ℝ), 
    (P.eval 1 = 1) ∧ 
    (∀ x : ℝ, x ≠ -7 → x + 1 ≠ 0 → P.eval (x + 1) ≠ 0 → 
      P.eval (2 * x) / P.eval (x + 1) = 8 - 56 / (x + 7)) ∧
    (P.eval (-1) = -5/21) := by
  use (Polynomial.C (1 / 21 : ℝ) * Polynomial.X ^ 3 + Polynomial.C (8 / 21 : ℝ) * Polynomial.X ^ 2 + Polynomial.C (12 / 21 : ℝ) * Polynomial.X)
  constructor
  · -- Check that P(1) = 1
    simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    <;> norm_num
  constructor
  · -- Check that the functional equation holds
    intro x hx1 hx2 hP
    have eq2 : (Polynomial.eval (2 * x) (Polynomial.C (1 / 21 : ℝ) * Polynomial.X ^ 3 + Polynomial.C (8 / 21 : ℝ) * Polynomial.X ^ 2 + Polynomial.C (12 / 21 : ℝ) * Polynomial.X)) / (Polynomial.eval (x + 1) (Polynomial.C (1 / 21 : ℝ) * Polynomial.X ^ 3 + Polynomial.C (8 / 21 : ℝ) * Polynomial.X ^ 2 + Polynomial.C (12 / 21 : ℝ) * Polynomial.X)) = 8 - 56 / (x + 7) := by 
      have h1 : x + 7 ≠ 0 := by
        intro h
        apply hx1
        linarith
      have h4 : (Polynomial.eval (2 * x) (Polynomial.C (1 / 21 : ℝ) * Polynomial.X ^ 3 + Polynomial.C (8 / 21 : ℝ) * Polynomial.X ^ 2 + Polynomial.C (12 / 21 : ℝ) * Polynomial.X)) = (8 * x^3 + 32 * x^2 + 24 * x) / 21 := by 
        simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
        <;> ring_nf
      have h5 : (Polynomial.eval (x + 1) (Polynomial.C (1 / 21 : ℝ) * Polynomial.X ^ 3 + Polynomial.C (8 / 21 : ℝ) * Polynomial.X ^ 2 + Polynomial.C (12 / 21 : ℝ) * Polynomial.X)) = (x^3 + 11 * x^2 + 31 * x + 21) / 21 := by
        simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
        <;> ring_nf
      rw [h4, h5]
      have h6 : (x + 7) ≠ 0 := h1
      have h7 : (x ^ 3 + 11 * x ^ 2 + 31 * x + 21) ≠ 0 := by
        by_contra h
        have hP0 : (Polynomial.eval (x + 1) (Polynomial.C (1 / 21 : ℝ) * Polynomial.X ^ 3 + Polynomial.C (8 / 21 : ℝ) * Polynomial.X ^ 2 + Polynomial.C (12 / 21 : ℝ) * Polynomial.X)) = 0 := by
          rw [h5]
          linarith
        contradiction
      field_simp [h6, h7]
      <;> ring_nf
      <;> field_simp
      <;> ring
    exact eq2
  · -- Check that P(-1) = -5/21
    simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    <;> norm_num