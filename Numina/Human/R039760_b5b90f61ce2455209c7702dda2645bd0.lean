import Mathlib

open Polynomial

/- 7th Australian 1986 Problem B3 A real polynomial of degree n > 2 has all roots real and positive. The coefficient of x n is 1, the coefficient of x n-1 is -1. The coefficient of x 1 is non-zero and -n 2 times the coefficient of x 0 . Show that all the roots are equal. -/
theorem algebra_147834 {n : ℕ} (hn : n > 2) (P : Polynomial ℝ) (hP : P.degree = n)
    (hP1 : P.coeff n = 1) (hP2 : P.coeff (n - 1) = -1) (hP3 : P.coeff 1 ≠ 0)
    (hP4 : P.coeff 1 = -n ^ 2 * P.coeff 0) (hr : P.roots.card = n)
    (hrpos : ∀ r, r ∈ P.roots → r > 0) :
    ∃ x, ∀ r ∈ P.roots, r = x := by
  have hdeg : P.natDegree = n :=  natDegree_eq_of_degree_eq_some hP
  -- Show that the sum of roots of P is 1.
  have hsum1 : P.roots.sum = 1 := by
    -- The result follows from Vieta's formula: the sum of roots is equal
    -- to -P.coeff (n - 1).
    rw [←neg_neg P.roots.sum, ←sum_roots_eq_nextCoeff_of_monic_of_split]
    · simp [nextCoeff, hdeg, show n ≠ 0 by linarith, hP2]
    · simp_rw [Monic, leadingCoeff, hdeg, hP1]
    · rw [splits_iff_card_roots, hr, hdeg]
  -- Show that the sum of inverses of roots of P is n ^ 2.
  have hsum2 : (P.roots.map (fun a : ℝ => 1 / a)).sum = n ^ 2 := by
    -- P.coeff 0 ≠ 0 because P.coeff 1 ≠ 0 and P.coeff 1 = -n^2 * P.coeff 0.
    have hP0 : P.coeff 0 ≠ 0 := by
      contrapose! hP3
      simp only [hP4, hP3, mul_zero]
    -- The trailing degree of P is 0 because P.coeff 0 ≠ 0.
    have hdeg' : P.natTrailingDegree = 0 := by
      apply natTrailingDegree_eq_of_trailingDegree_eq_some
      simp [trailingDegree_eq_zero, hP0]
    -- Prove the following general result:
    -- if we reverse coefficients of a polynomial then the roots of this reversed
    -- polynomial are inverses of roots of the original polynomial.
    have hrev : P.reverse.roots = P.roots.map (fun a => 1 / a) := by
      -- We can write P as a product of monomials X - C x for x ∈ P.roots
      -- and a polynomial q such that q has no roots.
      have ⟨q, hqp, hq_deg, hqr⟩ := Polynomial.exists_prod_multiset_X_sub_C_mul P
      -- P ≠ 0 because P.coeff 0 ≠ 0.
      have hp0 : P ≠ 0 := by
        rw [← coeff_natTrailingDegree_ne_zero, hdeg']
        exact hP0
      -- q ≠ 0 because P ≠ 0.
      have hq0 : q ≠ 0 := by
        contrapose! hp0
        rw [← hqp, hp0, mul_zero]
      -- 0 is not a root of P because P(0) = P.coeff 0 ≠ 0.
      have h0 : 0 ∉ P.roots := by simp [← coeff_zero_eq_eval_zero, hP0]
      -- The roots of P.reverse are the roots of (∏ x ∈ P.roots, (X - C x)).reverse
      -- plus roots of q.reverse (because (a * b).reverse = a.reverse * b.reverse).
      nth_rw 1 [← hqp, reverse_mul_of_domain, roots_mul]
      swap
      · rw [← reverse_mul_of_domain, ← leadingCoeff_ne_zero, reverse_leadingCoeff, hqp]
        simp [trailingCoeff.eq_1, hdeg', hP0]
      -- Show that q.reverse has no roots.
      have hq0 : q.reverse.roots = 0 := by
        -- Suppose that x is a root of q.reverse.
        ext x
        simp
        intro h
        -- Show that x⁻¹ ≠ 0.
        have hx0 : x⁻¹ ≠ 0 := by
          -- It is enough to show that x ≠ 0.
          simp only [ne_eq, inv_eq_zero]
          -- Supoose that x = 0 and show that q.reverse(0) ≠ 0.
          contrapose! h
          -- It is enought to show that q.reverse.coeff 0 ≠ 0.
          rw [h, ← coeff_zero_eq_eval_zero]
          -- q.reverse.coeff 0 = q.leadingCoeff ≠ 0 (because q ≠ 0).
          simp only [coeff_zero_reverse, ne_eq, leadingCoeff_eq_zero, hq0, not_false_eq_true]
        -- We get that x⁻¹ is invertible.
        have : Invertible x⁻¹ := invertibleOfNonzero hx0
        have heq : ⅟x⁻¹ = x := by simp
        revert h
        -- We have q.reverse(x) = q.reverse(1/x⁻¹) = 0 iff q(x⁻¹) = 0.
        rw [← heq, eval.eq_1, eval₂_reverse_eq_zero_iff, ← eval.eq_1, ← IsRoot.eq_1]
        -- We get that x⁻¹ is a root of q, a contradiction. So q.reverse has no roots.
        rw [← mem_roots hq0, hqr]
        simp only [Multiset.not_mem_zero, IsEmpty.forall_iff]
      -- Show that for any multiset s of polynomials, s.prod.reverse = (s.map (p => p.reverse)).prod
      -- (that is, the reverse of the product of polynomials in s is equal to the product of reverses of
      -- polynomials in s).
      have hprod (s : Multiset ℝ[X]) : s.prod.reverse = (s.map (fun p => p.reverse)).prod := by
        induction s using Multiset.induction with
        | empty =>
          simp only [Multiset.prod_zero, Multiset.map_zero]
          rw [show (1 : ℝ[X]) = C 1 by simp, reverse_C]
        | cons p ps ih => simp_all
      -- Show that (X - C c).reverse = C (-c) * X + C 1.
      have hrev1 (c : ℝ) : (X - C c).reverse = C (-c) * X + C 1 := by
        rw [show X - C c = C 1 * X + C (-c) by simp; ring, reverse_add_C]
        rw [reverse_mul_X, reverse_C, natDegree_C_mul_X _ (by norm_num)]
        ring
      simp only [hprod, Multiset.map_map, Function.comp_apply, hq0, add_zero]
      -- Show that the reverse of (P.roots.map (x => (X - C x).reverse)).prod
      -- is C a * (P.roots.map (fun x => 1 / x)).map (fun x => X - C x)).prod for
      -- some constant a ≠ 0.
      replace ⟨a, ha, hprod⟩ : ∃ a ≠ 0, (P.roots.map (fun x => (X - C x).reverse)).prod = C a * ((P.roots.map (fun x => 1 / x)).map (fun x => X - C x)).prod := by
        generalize P.roots = s at h0 ⊢
        -- Proof by induction on a multiset.
        induction s using Multiset.induction with
        | empty => use 1; simp
        | cons x xs ih =>
          simp only [Multiset.mem_cons, not_or] at h0
          have hx0 : x ≠ 0 := Ne.symm h0.1
          simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.map_map, Function.comp_apply]
          have ⟨a, ha, h⟩ := ih h0.2
          rw [h, hrev1]
          use a * -x
          refine ⟨by simp [ha, hx0], ?_⟩
          rw [mul_left_comm, ← mul_assoc, ← mul_assoc]
          congr 1
          · rw [mul_sub, ← map_mul]
            rw [show a * -x * (1 / x) = -a by field_simp]
            simp only [map_neg, neg_mul, map_one, mul_neg, map_mul, sub_neg_eq_add]
            ring
          · simp
      -- We showed that P.reverse is equal to the product of monomials in the form
      -- (X - C (1 / x)) where x is a root of P.
      -- We conclude that roots of P.reverse are inverses of roots of P.
      rw [hprod, roots_C_mul _ ha, roots_multiset_prod_X_sub_C]
    -- Let q = C (P.coeff 0)⁻¹ * P.reverse.
    set q := C (P.coeff 0)⁻¹ * P.reverse
    -- Roots of q are roots of P.reverse because P.coeff 0 ≠ 0.
    have hqr : q.roots = P.reverse.roots := by
      dsimp [q]
      rw [roots_C_mul _ (by simp [hP0])]
    -- The degree of q is equal to the degree of P.reverse
    -- which is equal to the degree of P (because P.coeff 0 ≠ 0).
    have hq_deg : q.natDegree = n := by
      apply eq_of_le_of_le
      · simp [q, natDegree_mul]
        apply le_trans natDegree_mul_le
        simp only [natDegree_C, zero_add, ← hdeg]
        exact reverse_natDegree_le P
      · have := card_roots' q
        apply le_trans _ (card_roots' q)
        rw [hqr, hrev, Multiset.card_map, hr]
    -- The sum of roots of q is equal to -q.coeff (n - 1) (from Vieta's formula).
    -- On the other hand, the sum of roots of q is equal to the sum of inverses of roots of P.
    rw [← hrev, ← hqr, ← neg_neg q.roots.sum, ← sum_roots_eq_nextCoeff_of_monic_of_split]
    -- Show that q.coeff (n - 1) = -n^2.
    · simp [nextCoeff, hq_deg, show n ≠ 0 by omega, q, coeff_reverse, hdeg, show n - (n - 1) = 1 by omega, hP4]
      -- We have q.coeff (n - 1) = (P.coeff 0)⁻¹ * P.coeff 1 = (P.coeff 0)⁻¹ * -n^2 * P.coeff 0 = -n^2.
      field_simp
    · simp_rw [Monic, q, leadingCoeff_mul, reverse_leadingCoeff, trailingCoeff, hdeg']
      simp [leadingCoeff_C, hP0]
    · rw [splits_iff_card_roots, hqr, hrev, Multiset.card_map, hr, hq_deg]
  -- Enumerate roots of P: find a function a from Fin n to ℝ such that a(i) = a root of P.
  -- More specifically, we need the following properties of a:
  -- a i > 0 for all i, ∑ i, a i = 1, ∑ i, 1 / a i = n^2, and ∀ r ∈ P.roots, ∃ j, r = a j.
  have ⟨a, ha0, ha1, ha2, har⟩ : ∃ a : Fin n → ℝ, (∀ i, a i > 0) ∧ ∑ i, a i = 1 ∧ ∑ i, 1 / a i = n ^ 2 ∧ ∀ r ∈ P.roots, ∃ j, r = a j := by
    -- Define g(i) = P.roots.toList[i] and take a = g.
    set g : Fin n → ℝ := fun i => P.roots.toList[i]'(by simp [hr])
    use g
    constructorm* _ ∧ _
    -- Show that g(i) > 0 for all i.
    · simp [g]
      intro i
      apply hrpos
      -- g(i) ∈ P.roots and we have that ∀ r ∈ P.roots, r > 0.
      rw [← Multiset.mem_toList]
      apply List.getElem_mem
    -- Show that ∑ g(i) = 1.
    · suffices ∑ i, g i = P.roots.toList.sum by simp [this, hsum1]
      -- We have P.roots.sum = P.roots.toList.sum and the result follows
      -- from P.roots.sum = 1.
      rw [← Fin.sum_univ_get]
      simp_rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr (by simp [hr])
      simp [hr, g]
    -- Show that ∑ 1 / g(i) = n^2.
    · suffices ∑ i, 1 / g i = (P.roots.map (fun a => 1 / a)).toList.sum by
        rw [this, Multiset.sum_toList, hsum2]
      -- It is enough to show that ∑ 1 / g(i) = (P.roots.map (fun a => 1 / a)).toList.sum
      -- (because (P.roots.map (fun a => 1 / a)).sum = n ^ 2).
      rw [← Multiset.coe_toList P.roots, Multiset.map_coe]
      simp only [one_div, Multiset.sum_toList, Multiset.sum_coe]
      -- After simplifications, we get the following goal:
      -- ∑ x : Fin n, (g x)⁻¹ = (List.map (fun a ↦ a⁻¹) P.roots.toList).sum.
      rw [← Fin.sum_univ_get]
      simp
      simp_rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr (by simp [hr])
      simp [hr, g]
    -- Show that for all r ∈ P.roots, there exists j such that r = g(j).
    · intro r
      rw [← Multiset.mem_toList]
      intro hr1
      apply List.getElem_of_mem at hr1
      have ⟨j, h, hj⟩ := hr1
      simp [hr] at h
      use ⟨j, h⟩
      simp [g, hj]
  -- Prove that there exists x such that a(i) = x for all i.
  have ⟨x, hax⟩ : ∃ x, ∀ i, a i = x := by
    have ha0' i : 0 ≤ a i := le_of_lt (ha0 i)
    have ha0'' i : √(a i) ≠ 0 := by
        rw [Real.sqrt_ne_zero']
        exact ha0 i
    -- Define a vector f in ℝ^n such that f(i) = √(a(i)).
    let f : EuclideanSpace ℝ (Fin n) := fun i : Fin n => √(a i)
    -- Define a vector g in ℝ^n such that g(i) = 1 / √(a(i)).
    let g : EuclideanSpace ℝ (Fin n) := fun i : Fin n => 1 / √(a i)
    have (i : Fin n) : f i = √(a i) := by simp
    -- We have ‖f‖ = √(∑ i, √(a(i)) ^ 2) = 1 (because ∑ i, a(i) = 1).
    have hf : ‖f‖ = 1 := by
      rw [norm_eq_sqrt_real_inner]
      simp [f, ← pow_two, Real.sq_sqrt, ha0', ha1]
    -- We have ‖g‖ = √(∑ i, 1 / √(a(i)) ^ 2) = √(n ^ 2) = n (because ∑ i, 1 / a(i) = n ^ 2).
    have hg : ‖g‖ = n := by
      rw [norm_eq_sqrt_real_inner]
      simp [g, ← pow_two, Real.sq_sqrt, ha0']
      simp_rw [← one_div, ha2]
      rw [Real.sqrt_sq (by simp)]
    -- Show that the inner product of f and g is ‖f‖ * ‖g‖.
    -- We have ⟪f, g⟫ = ∑ i, √(a(i)) * 1/√(a(i)) = ∑ i, 1 = n = 1 * n = ‖f‖ * ‖g‖.
    have hfg : ‖(inner f g : ℝ)‖ = ‖f‖ * ‖g‖ := by
      simp [hf, hg]
      simp [f, g, ha0'']
    -- f ≠ 0 because a(i) > 0 for all i.
    have hf0 : f ≠ 0 := by
      apply ne_zero_of_norm_ne_zero
      linarith
    -- g ≠ 0 because a(i) > 0 for all i.
    have hg0 : g ≠ 0 := by
      apply ne_zero_of_norm_ne_zero
      rw [hg]
      norm_cast
      omega
    -- Cauchy-Schwarz inequality implies that
    -- ⟪f, g⟫ ≤ ‖f‖ * ‖g‖ and the equality case happens when f and g are multiples of each other.
    -- We conclude that g = r • f for some r ≠ 0.
    rw [norm_inner_eq_norm_iff hf0 hg0] at hfg
    have ⟨r, hr0, hr⟩ := hfg
    -- Show that a(i) = 1 / r for all i.
    use 1 / r
    intro i
    have h := congr_arg (· * √(a i)) (congr_fun hr i)
    -- We have 1 / √(a(i)) = g(i) = r * f(i) = r * √(a(i)).
    -- So 1 = r * √(a(i)) ^ 2 = r * a(i) and a(i) = 1 / r.
    simp only [one_div, PiLp.smul_apply, smul_eq_mul, g, f, mul_assoc] at h
    rw [← pow_two, Real.sq_sqrt (ha0' i), inv_mul_cancel₀ (ha0'' i)] at h
    apply mul_left_cancel₀ hr0
    field_simp [h]
  -- We showed that a(i) = x for all i. It follows that for any r ∈ P.roots, r = x.
  use x
  intro r hr
  have ⟨j, hj⟩ := har r hr
  rw [hj, hax]