import Mathlib

/- The polynomial $P(x)$ is cubic.  What is the largest value of $k$ for which the polynomials
$Q_1(x) = x^2 + (k-29)x - k$ and $Q_2(x) = 2x^2 + (2k-43)x + k$ are both factors of $P(x)$? -/
theorem algebra_93486 : IsGreatest { k : ℝ | ∃ P : Polynomial ℝ, P.degree = 3 ∧
    Polynomial.X ^ 2 + Polynomial.C (k - 29) * Polynomial.X - Polynomial.C k ∣ P ∧
    Polynomial.C 2 * Polynomial.X ^ 2 + Polynomial.C (2 * k - 43) * Polynomial.X + Polynomial.C k ∣ P } 30 := by
  constructor
  swap
  . -- First, let's find an upper bound for $k$.
    rintro k ⟨P, hPdeg, hQ1, hQ2⟩
    let Q1 := Polynomial.X ^ 2 + Polynomial.C (k - 29) * Polynomial.X - Polynomial.C k
    let Q2 := Polynomial.C 2 * Polynomial.X ^ 2 + Polynomial.C (2 * k - 43) * Polynomial.X + Polynomial.C k
    have hPdeg : P.natDegree = 3 := by
      rw [← Polynomial.degree_eq_iff_natDegree_eq_of_pos (show 0 < 3 by norm_num)]
      exact hPdeg
    have hP_ne_zero := Polynomial.ne_zero_of_natDegree_gt (show 2 < P.natDegree by linarith)
    -- By inspection we see that both $Q_1$ and $Q_2$ have degree 2.
    have hQ1deg : Q1.natDegree = 2 := by simp [Q1]; compute_degree!
    have hQ2deg : Q2.natDegree = 2 := by simp [Q2]; compute_degree!
    have hQ1_ne_zero : Q1 ≠ 0 := Polynomial.ne_zero_of_natDegree_gt (show 1 < Q1.natDegree by linarith)
    have hQ2_ne_zero : Q2 ≠ 0 := Polynomial.ne_zero_of_natDegree_gt (show 1 < Q2.natDegree by linarith)
    -- Let S1 and S2 be the results of dividing P by Q1 and Q2, respectively. Since P
    -- has degree 3, S1 and S2 must have degree at most 1.
    obtain ⟨S1, hS1⟩ := hQ1
    obtain ⟨S2, hS2⟩ := hQ2
    have hS1_ne_zero : S1 ≠ 0 := fun h => by
      have : P = 0 := by rw [hS1, h]; simp
      exact hP_ne_zero this
    have hS2_ne_zero : S2 ≠ 0 := fun h => by
      have : P = 0 := by rw [hS2, h]; simp
      exact hP_ne_zero this
    have hS1deg : S1.natDegree = 1 := by
      have := calc
        3 = (Q1 * S1).natDegree := by simp only [Q1]; rw [← hS1, hPdeg]
        _ = Q1.natDegree + S1.natDegree := Polynomial.natDegree_mul hQ1_ne_zero hS1_ne_zero
        _ = 2 + S1.natDegree := by rw [hQ1deg]
      linarith
    have hS2deg : S2.natDegree = 1 := by
      have := calc
        3 = (Q2 * S2).natDegree := by simp only [Q2]; rw [← hS2, hPdeg]
        _ = Q2.natDegree + S2.natDegree := Polynomial.natDegree_mul hQ2_ne_zero hS2_ne_zero
        _ = 2 + S2.natDegree := by rw [hQ2deg]
      linarith
    -- Thus S1 = ax + b and S2 = cx + d for some a, b, c, d.
    obtain ⟨a, b, hab⟩ := Polynomial.exists_eq_X_add_C_of_natDegree_le_one (show S1.natDegree ≤ 1 by linarith)
    obtain ⟨c, d, hcd⟩ := Polynomial.exists_eq_X_add_C_of_natDegree_le_one (show S2.natDegree ≤ 1 by linarith)
    -- Now we can compute the coefficients of P in terms of a, b or c, d and equate them.
    -- True ∧ (-29 + k) * a = k * a - a * 29 ∧ (-29 + k) * b - k * a = 7 ∧ -(k * b) = 8
    obtain ⟨hleft3, hleft2, hleft1, hleft0⟩ :
        P.coeff 3 = a ∧ P.coeff 2 = (k - 29) * a + b ∧ P.coeff 1 = - k * a + (k - 29) * b ∧ P.coeff 0 = - k * b := by
      rw [hS1, hab]
      ring_nf
      simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_mul_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
      simp
      ring_nf
      simp
    obtain ⟨hright3, hright2, hright1, hright0⟩:
        P.coeff 3 = 2 * c ∧ P.coeff 2 = (2 * k - 43) * c + 2 * d ∧ P.coeff 1 = k * c + (2 * k - 43) * d ∧ P.coeff 0 = k * d := by
      rw [hS2, hcd]
      ring_nf
      simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_mul_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
      simp
      ring_nf
      simp
    -- From the constant term we have either k = 0 or b = -d. Clearly if k ≤ 0 then k ≤ 30,
    -- so we continue with k > 0.
    cases le_or_gt k 0 with
    | inl hk => linarith
    | inr hk =>
      -- From the coefficient of x^3
      have eq1 : a = 2 * c := by linarith
      -- From constant coefficient
      have eq2 : k * b = k * (-d) := by linarith
      rw [mul_left_cancel_iff_of_pos hk] at eq2
      -- From the coefficient of x^2
      have : (k - 29) * a + b - (2 * k - 43) * c - 2 * d = 0 := by linarith
      rw [eq1, eq2] at this
      have eq3 : d = -5 * c := by linarith
      -- From the coefficient of x
      have : k * c + (2 * k - 43) * d - (- k * a + (k - 29) * b) = 0 := by linarith
      simp [eq1, eq2, eq3] at this
      have eq4 : c * (k * 12 - 360) = 0 := by linarith
      -- From this either c = 0 or k = 30. We know c ≠ 0 since the degree of S2 is 1, therefore k = 30.
      have : S2.leadingCoeff = c := by
          rw [← Polynomial.coeff_natDegree, hS2deg, hcd]
          simp
      have : c ≠ 0 := by
        rw [← this, Polynomial.leadingCoeff_ne_zero]
        exact hS2_ne_zero
      simp [this] at eq4
      linarith
  . -- We check that k = 30 indeed works, using the equations above (and arbitrarily choosing c = 1).
    let k : ℝ := 30
    let P : Polynomial ℝ := Polynomial.C 2 * Polynomial.X ^ 3 + Polynomial.C 7 * Polynomial.X ^ 2 - Polynomial.C 55 * Polynomial.X - Polynomial.C 150
    let Q1 : Polynomial ℝ := Polynomial.X ^ 2 + Polynomial.C (k - 29) * Polynomial.X - Polynomial.C k
    let Q2 : Polynomial ℝ := Polynomial.C 2 * Polynomial.X ^ 2 + Polynomial.C (2 * k - 43) * Polynomial.X + Polynomial.C k
    let S1 : Polynomial ℝ := Polynomial.C 2 * Polynomial.X + Polynomial.C 5
    let S2 : Polynomial ℝ := Polynomial.X - Polynomial.C 5
    -- Is there a tactic that can multiply polynomials?
    have hS1 : Q1 * S1 = P := by
      simp only [Q1, S1, P, k]
      norm_num
      simp only [Polynomial.C_mul_X_pow_eq_monomial, Polynomial.C_mul_X_eq_monomial]
      simp only [← Polynomial.monomial_one_one_eq_X, ← Polynomial.monomial_zero_left, sub_eq_add_neg, ← Polynomial.monomial_neg]
      ring_nf
      simp only [Polynomial.monomial_pow, Polynomial.monomial_mul_monomial]
      ring_nf
      move_add [← Polynomial.monomial 3 2, ← Polynomial.monomial 2 5]
      nth_rw 2 [add_assoc]; rw [← Polynomial.monomial_add]
      nth_rw 3 [add_assoc]; rw [← Polynomial.monomial_add]
      ring_nf
    have hS2 : Q2 * S2 = P := by
      simp only [Q2, S2, P, k]
      norm_num
      simp only [Polynomial.C_mul_X_pow_eq_monomial, Polynomial.C_mul_X_eq_monomial]
      simp only [← Polynomial.monomial_one_one_eq_X, ← Polynomial.monomial_zero_left, sub_eq_add_neg, ← Polynomial.monomial_neg]
      ring_nf
      simp only [Polynomial.monomial_mul_monomial]
      ring_nf
      nth_rw 2 [add_assoc]; rw [← Polynomial.monomial_add]
      nth_rw 3 [add_assoc]; rw [← Polynomial.monomial_add]
      ring_nf
    use P
    and_intros
    . simp [P]; compute_degree!
    . simp [P]; simp [P, Q1, S1] at hS1; exact Dvd.intro S1 hS1
    . simp [P]; simp [P, Q2, S2] at hS2; exact Dvd.intro S2 hS2