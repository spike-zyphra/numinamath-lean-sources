import Mathlib

open Polynomial

/- Find the remainder when the polynomial $x^5 + x^4 + x^3 + x^2 + x$ is divided by $x^3-4x$. -/
theorem algebra_22270 {f g : Polynomial ℝ} (hf : f = X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X)
    (hg : g = X ^ 3 - 4 * X) :
    f % g = 5 * X ^ 2 + 21 * X := by
  -- $f = (X^2 + X + 5) g + (5 X ^ 2 + 21 X)$
  have feq1 : f = (X ^ 2 + X + 5) * g + (5 * X ^ 2 + 21 * X) := by
    rw [hf, hg]
    ring
  rw [hf, hg]
  have feq2 : f = f / g * g + f % g := by
    exact Eq.symm (EuclideanDomain.div_add_mod' f g)
  have eq : (f % g - (5 * X ^ 2 + 21 * X)) - g * ((X ^ 2 + X + 5) - f / g) = f / g * g + f % g - ((X ^ 2 + X + 5) * g + (5 * X ^ 2 + 21 * X)) := by
    ring_nf
  rw [← feq1, ← feq2, sub_self] at eq
  apply eq_of_sub_eq_zero at eq
  have eq2 := eq
  apply congrArg (fun x ↦ x.natDegree) at eq
  -- $\deg(g) = 3$
  have gdeg : g.natDegree = 3 := by
    rw [hg]
    rw [natDegree_sub_eq_left_of_natDegree_lt ?_]
    simp only [natDegree_pow, natDegree_X, mul_one]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, natDegree_mul_X, zero_add, natDegree_pow, natDegree_X, mul_one, Nat.one_lt_ofNat]
    show natDegree (C 4) + 1 < 3
    simp only [natDegree_C, zero_add, Nat.one_lt_ofNat]
  -- $g \neq 0$
  have gne : g ≠ 0 := by
    by_contra contra
    apply congrArg (fun x ↦ x.natDegree) at contra
    simp only [gdeg, natDegree_zero, OfNat.ofNat_ne_zero] at contra
  -- $f / g = X^2 + X + 5$
  have diveq : (X ^ 2 + X + 5) - f / g = 0 := by
    by_contra contra
    rw [natDegree_mul gne contra] at eq
    have : (f % g - (5 * X ^ 2 + 21 * X)).natDegree ≤ 2
    rw [sub_eq_add_neg, natDegree_add_le_iff_right, natDegree_neg, natDegree_add_eq_left_of_degree_lt]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, natDegree_mul_X_pow, zero_add, le_refl]
    show natDegree (C 5) + 2 ≤ 2
    simp only [natDegree_C, zero_add, le_refl]
    show (C 21 * X : ℝ[X]).degree < (C 5 * X ^ 2 : ℝ[X]).degree
    simp only [degree_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, degree_C, degree_X, zero_add, degree_pow, nsmul_eq_mul, Nat.cast_ofNat, mul_one, Nat.one_lt_ofNat]
    -- the degree of remainder is less than the degree of divisor
    have remdeglt : (f % g).natDegree < g.natDegree := by
      have natDegree_mod_lt (p : Polynomial ℝ) {q : Polynomial ℝ} (hq : q.natDegree ≠ 0) :
      (p % q).natDegree < q.natDegree := by
        have hq' : q.leadingCoeff ≠ 0 := by
          rw [leadingCoeff_ne_zero]
          contrapose! hq
          simp [hq]
        rw [mod_def]
        refine (natDegree_modByMonic_lt p ?_ ?_).trans_le ?_
        · refine monic_mul_C_of_leadingCoeff_mul_eq_one ?_
          rw [mul_inv_eq_one₀ hq']
        · contrapose! hq
          rw [← natDegree_mul_C_eq_of_mul_eq_one ((inv_mul_eq_one₀ hq').mpr rfl)]
          simp [hq]
        · exact natDegree_mul_C_le q q.leadingCoeff⁻¹
      refine natDegree_mod_lt f ?_
      linarith
    linarith
    linarith
  -- so $f % g = X ^ 3 - 4 * X$
  rw [diveq, mul_zero] at eq2
  apply eq_of_sub_eq_zero at eq2
  rw [← hf, ← hg, eq2]