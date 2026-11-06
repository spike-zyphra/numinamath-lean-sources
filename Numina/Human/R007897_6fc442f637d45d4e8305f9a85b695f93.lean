import Mathlib

open Polynomial

/- The polynomial $f(x)$ is divided by the polynomial $d(x)$ to give a quotient of $q(x)$ and a remainder of $r(x)$. If $\deg f = 9$ and $\deg r = 3$, what is the maximum possible value of $\deg q$? -/
theorem algebra_20681 {f d q r : Polynomial ℝ} (hf : f.natDegree = 9) (hqeq : q = f / d) (hreq : r = f % d) (hr : r.natDegree = 3) : q.natDegree ≤ 5 := by
  if hq : q = 0 then
    rw [hq]
    exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N => congrFun rfl
  else
  -- $d \neq 0$
  have hd : d ≠ 0 := by
    by_contra contra
    rw [contra, EuclideanDomain.div_zero] at hqeq
    contradiction
  -- $\deg(d) \neq 0$
  have hddeg : d.natDegree ≠ 0 := by
    by_contra contra
    apply Polynomial.eq_C_of_natDegree_eq_zero at contra
    rw [contra] at hreq
    have dcoene : d.coeff 0 ≠ 0 := by
      by_contra contra1
      rw [contra1] at contra
      rw [map_zero] at contra
      contradiction
    have : f % Polynomial.C (d.coeff 0) = 0 := by
      simp only [EuclideanDomain.mod_eq_zero]
      use Polynomial.C (d.coeff 0)⁻¹ * f
      rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ dcoene, map_one, one_mul]
    rw [this] at hreq
    rw [hreq] at hr
    simp only [Polynomial.natDegree_zero, OfNat.zero_ne_ofNat] at hr
  -- $f = dq + r$
  have heq : f = d * q + r := by
    rw [hqeq, hreq]
    exact Eq.symm (EuclideanDomain.div_add_mod f d)
  -- the degree of remainder $r$ is less than the divisor $d$
  have hdr : d.natDegree > r.natDegree := by
    rw [hreq]
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
    exact natDegree_mod_lt f hddeg
  -- Since $\deg f = 9$ and $\deg r = 3$, we must have $\deg q + \deg d = 9$
  have h1 : f.natDegree = d.natDegree + q.natDegree := by
    rw [heq, Polynomial.natDegree_add_eq_left_of_degree_lt, Polynomial.natDegree_mul]
    exact Polynomial.ne_zero_of_natDegree_gt hdr
    exact hq
    rw [Polynomial.degree_mul]
    refine lt_add_of_lt_of_nonneg ?_ ?_
    exact Polynomial.degree_lt_degree hdr
    exact Polynomial.zero_le_degree_iff.mpr hq
  -- Since $\deg d = 9 - \deg q$, we must have $\deg q \leq 5$
  linarith [hf, h1]
