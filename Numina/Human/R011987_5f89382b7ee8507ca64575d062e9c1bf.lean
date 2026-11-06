import Mathlib

open Polynomial

/- 10.5. Let $P(X)$ be a polynomial with real coefficients, such that

$x \cdot P(x+2022)-(x+2023) \cdot P(x)=2022 \cdot x-2023$, for any $x \in \mathbb{R}$. Find the remainder of the division of the polynomial $P(X)$ by the polynomial $Q(X)=X^{2}+X$. -/
theorem algebra_166627 {P : Polynomial ℝ} (hP : ∀ x, x * P.eval (x + 2022) - (x + 2023) * P.eval x = 2022 * x - 2023) :
    P % (X ^ 2 + X) = -2022 * X + 1 := by
  -- let's name the target R for ease of work
  set R := P % (X ^ 2 + X) with hR
  -- by using the equation at 0 and -2023, we get values of P at 0 and -1
  have hP_zero : P.eval 0 = 1 := by
    specialize hP 0
    simpa using hP
  have hP_neg_one : P.eval (-1) = 2023 := by
    specialize hP (-2023)
    simp at hP
    ring_nf at hP
    linarith
  -- degree of X^2 + X is 2 and it is a monic polynomial
  have h_deg : (X^2 + X : ℝ[X]).natDegree = 2 := by compute_degree!
  have h_monic : (X ^ 2 + X : ℝ[X]).Monic := by
    rw [Monic.def, ← coeff_natDegree, h_deg]
    simp
    exact coeff_X_of_ne_one (by norm_num)
  -- now R's degree is less than 2 as it is remainder from divsiro with degree 2
  have hR_deg : R.natDegree < 2 := by
    rw [hR]
    convert natDegree_mod_lt P (show (X^2 + X : ℝ[X]).natDegree ≠ 0 by linarith)
    rw [h_deg]
  -- write R as monic division
  replace hR : R = P %ₘ (X ^ 2 + X) := by
    rw [hR]
    exact Eq.symm (modByMonic_eq_mod P (by assumption))
  -- next write R as P - (X^2 + X) * (P / (X^2 + X))
  replace hR : R = P - (X ^ 2 + X) * (P /ₘ (X ^ 2 + X)) := by
    rw [hR, modByMonic_eq_sub_mul_div P h_monic]
  -- now using P's values at 0, -1, we get values of R at 0, -1 as these are roots of X^2 + X
  have hR_zero : R.eval 0 = 1 := by
    rw [hR]
    simp [hP_zero]
  have hR_neg_one : R.eval (-1) = 2023 := by
    rw [hR]
    simp [hP_neg_one]
  -- since R's degree is less than 2, we write it as ax + b
  have hR_linear : R =  C (R.coeff 1) * X + C (R.coeff 0) := by
    have := R.as_sum_range' 2 hR_deg
    rw [Finset.sum_range, Fin.sum_univ_two] at this
    rw [← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial] at this
    simp at this
    linear_combination this
  -- now using the values, we get a = -2022, b = 1
  rw [hR_linear] at hR_zero hR_neg_one
  simp at hR_zero hR_neg_one
  rw [show R.coeff 1 = -2022 by linarith, show R.coeff 0 = 1 by linarith] at hR_linear
  norm_cast at hR_linear ⊢