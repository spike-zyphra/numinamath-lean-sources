import Mathlib

open Polynomial

theorem algebra_7880 {p : ℝ[X]} (hp : ∀ x, p.eval (x + 1) = x^2 - x + 2 * p.eval 6) :
    p.coeff 0 + p.coeff 1 + p.coeff 2 = -40 := by

  have eq4 : p.eval 6 = -20 := by
    have eq2 := hp 5
    norm_num at eq2 ⊢
    linarith

  have eq3 : p.eval 1 = 2 * p.eval 6 := by
    have eq1 := hp 0
    norm_num at eq1 ⊢
    linarith

  have eq5 : p.eval 1 = -40 := by
    rw [eq4] at eq3
    linarith

  have eq13 : p.natDegree = 2 := by
    have h1 : ∀ (y : ℝ), p.eval y = y ^ 2 - 3 * y + (2 + 2 * p.eval 6 : ℝ) := by
      intro y
      have eq14 := hp (y - 1 : ℝ)
      have eq15 : p.eval ((y - 1 : ℝ) + 1) = (y - 1 : ℝ) ^ 2 - (y - 1 : ℝ) + 2 * p.eval 6 := eq14
      have eq16 : p.eval y = (y - 1 : ℝ) ^ 2 - (y - 1 : ℝ) + 2 * p.eval 6 := by 
        have eq17 : p.eval ((y - 1 : ℝ) + 1) = p.eval y := by
          ring_nf
        rw [eq17] at eq15
        linarith
      have eq17 : (y - 1 : ℝ) ^ 2 - (y - 1 : ℝ) = y ^ 2 - 3 * y + 2 := by
        ring_nf
      have eq18 : (y - 1 : ℝ) ^ 2 - (y - 1 : ℝ) + 2 * p.eval 6 = y ^ 2 - 3 * y + (2 + 2 * p.eval 6 : ℝ) := by
        linarith [eq17]
      linarith [eq16, eq18]

    have h2 : p.natDegree = 2 := by
      have eq14 : p = Polynomial.X ^ 2 + Polynomial.C (-3 : ℝ) * Polynomial.X + Polynomial.C (2 + 2 * p.eval 6 : ℝ) := by
        apply Polynomial.funext
        intro x
        simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
        specialize h1 x
        linarith
      rw [eq14]
      compute_degree <;> norm_num

    exact h2

  have eq26 : p.eval 1 = p.coeff 0 + p.coeff 1 + p.coeff 2 := by
    have h10 : p.natDegree = 2 := eq13
    simp [Polynomial.eval_eq_sum_range, h10, Finset.sum_range_succ]

  linarith [eq26, eq5]