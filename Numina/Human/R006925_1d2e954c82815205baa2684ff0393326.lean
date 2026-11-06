import Mathlib

/- Suppose that $P(z), Q(z)$ and $R(z) are polynomials with real coefficients,
having degrees 2, 3, and 6 respectively, and constant terms 1, 2, and 3 respectively.
Let $N$ be the number of distinct complex numbers $z$ that satisfy the
equation $P(z) ⋅ Q(z) = R(z)$. What is the minimum possible value of $N$? -/
theorem algebra_94876 : IsLeast {N | ∃ P Q R : Polynomial ℝ,
    P.degree = 2 ∧ Q.degree = 3 ∧ R.degree = 6 ∧ P.coeff 0 = 1 ∧ Q.coeff 0 = 2 ∧ R.coeff 0 = 3 ∧
    N = {z : ℂ | (P.map Complex.ofRealHom).eval z * (Q.map Complex.ofRealHom).eval z = (R.map Complex.ofRealHom).eval z}.ncard} 1 := by
  and_intros
  swap
  . rintro N ⟨P, Q, R, hdegP, hdegQ, hdegR, hP0, hQ0, hR0, hN⟩
    rw [hN]
    let P' := P.map Complex.ofRealHom
    let Q' := Q.map Complex.ofRealHom
    let R' := R.map Complex.ofRealHom
    -- Note $z$ is in the set iff it is a root of $R - P * Q$
    let S := P' * Q' - R'
    have : {z : ℂ | P'.eval z * Q'.eval z = R'.eval z} = {z : ℂ | Polynomial.IsRoot S z} := by
      ext z
      simp [S]
      rw [sub_eq_zero]
    rw [this]
    -- $P * Q - R$ has degree 6, so it is nonconstant and thus has a finite set of roots,
    -- and at least one root by the fundamental theorem of algebra
    have S_degree : 0 < S.degree := by
      simp [S]
      have : (P' * Q').degree < R'.degree := by simp [P', Q', R', hdegP, hdegQ, hdegR]; norm_num
      rw [Polynomial.degree_sub_eq_right_of_degree_lt this]
      simp [R']
      rw [hdegR]
      norm_num
    rw [Nat.succ_le]
    rw [Set.ncard_pos (Polynomial.finite_setOf_isRoot (Polynomial.ne_zero_of_degree_gt S_degree))]
    exact Complex.exists_root S_degree
  . -- Now need to give polynomials $P$, $Q$, and $R$ for which the conditions are true
    -- and the bound is achieved.
    let P : Polynomial ℝ := Polynomial.X ^ 2 + 1
    let Q : Polynomial ℝ := Polynomial.X ^ 3 + 2
    let R : Polynomial ℝ := (Polynomial.X + 1) ^ 6 + P * Q
    use P
    use Q
    use R
    and_intros
    . simp [P, Q, R]; compute_degree! -- Degree of P is 2
    . simp [P, Q, R]; compute_degree! -- Degree of Q is 3
    . simp [P, Q, R]; compute_degree! -- Degree of R is 6
    . simp [P, Q, R] -- Constant term of P is 1
    . simp [P, Q, R] -- Constant term of Q is 2
    . simp [P, Q, R, pow_succ]; norm_num -- Constant term of R is 3
    . -- The set of roots of P * Q - R has cardinality 1 since it is the singleton set {1}
      have : {z | (P.map Complex.ofRealHom).eval z * (Q.map Complex.ofRealHom).eval z = (R.map Complex.ofRealHom).eval z} = {-1} := by
        ext z
        simp [R]
        exact add_eq_zero_iff_eq_neg
      symm
      calc
        {z | (P.map Complex.ofRealHom).eval z * (Q.map Complex.ofRealHom).eval z = (R.map Complex.ofRealHom).eval z}.ncard = ({-1} : Set ℂ).ncard := by rw [this]
        _ = 1 := by simp