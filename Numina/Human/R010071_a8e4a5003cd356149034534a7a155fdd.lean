import Mathlib

open Polynomial

/-- Find the sum of the roots, real and non-real, of the equation x^2001 + (1/2-x)^2001,
    given that there are no multiple roots. -/
theorem algebra_97559 : (X ^ 2001 + (C (1 / 2) - X) ^ 2001 : Polynomial ℂ).roots.sum = 500 := by
  let P : Polynomial ℂ := X ^ 2001 + (C (1 / 2) - X) ^ 2001
  -- show that P is not zero to avoid edge cases
  have nz : P ≠ 0 := by
    have : P.eval 0 ≠ 0 := by
      unfold P
      simp
    intro eq
    simp[eq] at this

  -- rearrange coefficients
  have P_eq : P = (X : Polynomial ℂ) ^ 2001 - (X + (C (- 1/2))) ^ 2001 := by
    unfold P
    congr
    rw[neg_eq_neg_one_mul]
    have odd : Odd 2001 := by exists 1000
    rw[← odd.neg_one_pow, ← mul_pow, ← neg_eq_neg_one_mul, neg_add, ← C_neg, neg_div, neg_neg, sub_eq_neg_add]
  -- from the Binomial Theorem, the first term of (1/2 - x)^2001 is -x^2001, but x^2001 - x^2001 is 0,
  -- so the term with the largest degree is x^2000
  have coeff2001 : P.coeff 2001 = 0 := by
    rw[P_eq, coeff_sub, coeff_X_add_C_pow]
    simp
  -- So we need the coefficient of that term, which is
  -- $\binom{2001} 1 (-x)^{2000} (1/2)^1 = \frac{2001 x^{2000}}{2}
  have coeff2000 : P.coeff 2000 = 2001 / 2 := by
    rw[P_eq, coeff_sub, coeff_X_add_C_pow]
    simp only [coeff_X_pow, Nat.reduceEqDiff, ↓reduceIte, Nat.reduceSub, pow_one,
      Nat.choose_succ_self_right, Nat.reduceAdd, Nat.cast_ofNat, zero_sub]
    ring
  -- as well as the coefficient of x^1999, which is
  -- $\binom{2001} 2 (-x)^{1999} (1/2)^2 = \frac{-x^{1999} \dot 2001 \dot 2000}{8} = -2001 \cdot 250 x^{1999}$
  have coeff1999 : P.coeff 1999 = - 2001 * 250 := by
    rw[P_eq, coeff_sub, coeff_X_add_C_pow]
    simp only [coeff_X_pow, Nat.reduceEqDiff, ↓reduceIte, Nat.reduceSub, zero_sub, neg_mul, neg_inj]
    have : (- 1 / (2 : ℂ)) ^ 2 = 4 ⁻¹ := by norm_num
    rw[this]
    have : 2001 = 2 + 1999 := by norm_num
    rw[this, ← Nat.choose_symm_add, Nat.choose_two_right]
    norm_num

  have : P.natDegree ≤ 2001 := by
    rw[P_eq]
    compute_degree!
  -- Clearly, P must have degree 2000
  have P_degree : P.natDegree = 2000 := by
    have : P.natDegree ≠ 2001 := by
      intro eq
      have : P.degree = ↑ (2001 : ℕ) := by rwa[degree_eq_iff_natDegree_eq nz]
      exact coeff_ne_zero_of_eq_degree this coeff2001
    have : P.natDegree ≤ 2000 := by omega
    apply natDegree_eq_of_le_of_coeff_ne_zero this
    simp[coeff2000]
  
  have div_monic : Monic (C (2 / 2001) * P) := by
    rw[Monic, leadingCoeff, natDegree_C_mul, P_degree]
    simp[coeff2000]
    simp
  -- and from Vieta's formulas, we see that the sum of the roots is of the form -a_{n-1}/a_n,
  -- where a_n is the leading coefficient. Hence for monic polynomials, it is -a_{n-1}, which we utilize
  -- by normalizing our polynomial.
  have : (C (2 / 2001) * P).roots.sum = 500 := by
    rw[← neg_inj, ← sum_roots_eq_nextCoeff_of_monic_of_split div_monic, nextCoeff_of_natDegree_pos,
      natDegree_C_mul, P_degree]
    simp[coeff1999]
    norm_num
    · simp
    · simp[natDegree_C_mul, P_degree]
    · apply IsAlgClosed.splits
  rw[← this]
  congr 1
  -- since a nonzero multiple of a polynomial and itself have the same roots, we can compute the sum
  -- of the original polynomial.
  rw[Polynomial.roots_C_mul P (by simp)]