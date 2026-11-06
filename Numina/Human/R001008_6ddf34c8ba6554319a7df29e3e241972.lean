import Mathlib

open Polynomial

/- For specific positive numbers $m$ and $n$, the quadratics $16X^2+36X+56$ and $(mX+n)^2$ differ only in their constant term. What is $mn$? -/
theorem algebra_19782 {m n : ℝ} (hm : 0 < m) (hn : 0 < n) (h : ∃ c : ℝ, C 16 * X ^ 2 + C 36 * X + C 56 + C c = (C m * X + C n) ^ 2) :
    m * n = 18 := by
  rcases h with ⟨c, h⟩
  -- equate the coefficients of $X ^ 2$ to get $16 = m ^ 2$, so $m = 4$
  have meq : m = 4 := by
    apply congrArg (fun x ↦ x.coeff 2) at h
    rw [add_sq, mul_pow, ← C_pow, ← C_pow] at h
    simp only [coeff_add, coeff_C_mul, coeff_X_pow, ↓reduceIte, mul_one, coeff_mul_X, coeff_C_succ, add_zero, coeff_mul_C, coeff_ofNat_mul, mul_zero, zero_mul] at h
    have mid : (16 : ℝ) = 4 ^ 2 := by
      ring
    rw [mid] at h
    apply eq_or_eq_neg_of_sq_eq_sq at h
    rcases h with h | h
    exact h.symm
    linarith
  -- equate the coefficients of $X$ to get $36 = 2mn$, so $n = 9 / 2$
  have neq : n = 9 / 2 := by
    apply congrArg (fun x ↦ x.coeff 1) at h
    rw [add_sq, mul_pow, ← C_pow, ← C_pow] at h
    simp only [coeff_add, coeff_C_mul, coeff_X_pow, OfNat.one_ne_ofNat, ↓reduceIte, mul_zero, coeff_mul_X, coeff_C_zero, zero_add, coeff_C_succ, add_zero, coeff_mul_C, coeff_ofNat_mul, meq] at h
    linarith
  rw [meq, neq]
  ring