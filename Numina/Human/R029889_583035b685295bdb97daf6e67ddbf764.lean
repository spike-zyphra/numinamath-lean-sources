import Mathlib

open Polynomial

/- For certain real values of $a, b, c,$ and $d_{},$
the equation $x^4+ax^3+bx^2+cx+d=0$ has four non-real roots.
The product of two of these roots is $13+i$ and the sum of the other two roots is $3+4i,$
where $i=\sqrt{-1}.$  Find $b.$ -/
theorem algebra_96504 {a b c d : ℝ} {w x y z : ℂ} (p : ℝ[X])
    (hp : p = X ^ 4 + C a * X ^ 3 + C b * X ^ 2 + C c * X + C d)
    (hp_roots : p.roots = 0)
    (hp_aroots : p.aroots ℂ = {w, x, y, z})
    (hprod : y * z = 13 + .I) (hsum : w + x = 3 + 4 * .I) :
    b = 51 := by
  -- The degree of p is 4.
  have hdeg : p.natDegree = 4 := by simp [hp]; compute_degree!
  -- p is monic.
  have hp1 : p.leadingCoeff = 1 := by simp_rw [leadingCoeff, hdeg, hp]; compute_degree!
  -- p ≠ 0 (because its degree > 0).
  have hp0 : p ≠ 0 := by
    apply ne_zero_of_natDegree_gt (n := 0)
    simp [hdeg]
  -- Show that x ≠ w* (complex conjugate of w).
  have hxw : x ≠ starRingEnd ℂ w := by
    -- Suppose that x = w*.
    by_contra h
    -- Then we have 13 + I = w + x = w + w* = 2 * w.re.
    -- This is impossible because 2 * w.re is a real number.
    rw [h, Complex.add_conj] at hsum
    apply_fun Complex.im at hsum
    simp at hsum
  -- Show that if r is a complex root of p then r has a non-zero imaginary part.
  have hr {r} (hr : r ∈ p.aroots ℂ) : r.im ≠ 0 := by
    simp at hr
    -- Suppose that r.im = 0.
    contrapose! hp_roots
    have ⟨_, hr⟩ := hr
    -- Then we get r = r.re.
    have h : r = algebraMap ℝ ℂ r.re := by
      nth_rw 1 [← Complex.re_add_im r, hp_roots]
      simp
    -- r.re is a complex root of p ∈ ℂ[X] but then r.re is also a root of p ∈ ℝ[X].
    rw [h, aeval_ofReal] at hr
    simp at hr
    -- On the other hand, we have p.roots = 0 (for p ∈ ℝ[X]), a contradiction.
    rw [← Multiset.card_pos, Multiset.card_pos_iff_exists_mem]
    use r.re
    simp [hr]
    assumption
  -- Prove that complex roots of p are {w, w*, x, x*}.
  have hroots : p.aroots ℂ = {w, starRingEnd ℂ w, x, starRingEnd ℂ x} := by
    have hw : w ∈ p.aroots ℂ := by simp [hp_aroots]
    have hw0 : p.aeval w = 0 := by
      simp [mem_aroots, hp0] at hw
      exact hw
    -- w is a complex root of p and w.im ≠ 0, so p can be factored as follows:
    -- p = (X ^ 2 - (2 * w.re) * X + ‖w‖^2) * q for some q ∈ ℝ[X].
    have ⟨q, hpq⟩ := quadratic_dvd_of_aeval_eq_zero_im_ne_zero p hw0 (hr hw)
    -- Show that complex roots of X ^ 2 - (2 * z.re) * X + ‖z‖^2) are {z, z*}
    -- for any complex number z.
    have h2 (z : ℂ) : (X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2)).aroots ℂ = {z, starRingEnd ℂ z} := by
      -- Show the following equality for polynomials in ℂ[X]:
      -- (X - z) * (X - z*) = X^2 - (2 * z.re) * X + ‖z‖^2.
      have eq : (X - C z) * (X - C (starRingEnd ℂ z)) = (X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2)).map (algebraMap ℝ ℂ) := calc
        (X - C z) * (X - C (starRingEnd ℂ z)) = X ^ 2 - C (z + starRingEnd ℂ z) * X + C (z * starRingEnd ℂ z) := by
            simp only [map_add, map_mul]
            ring
        _ = (X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2)).map (algebraMap ℝ ℂ) := by
            rw [Complex.add_conj, Complex.mul_conj, ← Complex.sq_abs]
            simp
      -- Roots of (X - z) * (X - z*) are {z, z*}, so the complex roots of
      -- X^2 - (2 * z.re) * X + ‖z‖^2 are {z, z*}.
      simp_rw [aroots, ← eq]
      rw [roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _))]
      simp only [roots_X_sub_C, Multiset.singleton_add, Multiset.insert_eq_cons]
    -- We get that complex roots of p are {w, w*} + complex roots of q.
    have h : p.aroots ℂ = {w, starRingEnd ℂ w} + q.aroots ℂ := by
      rw [hpq, aroots_mul (by rwa [← hpq]), h2]
    -- Show that x is a complex root of q.
    have hx0 : q.aeval x = 0 := by
      -- We know that complex roots of p are {w, x, y, z}.
      -- We also showed that complex roots of p are {w, w*} + complex roots of q.
      simp [hp_aroots] at h
      -- So x ∈ {w*} + complex roots of q.
      have hx : x ∈ (starRingEnd ℂ) w ::ₘ q.aroots ℂ := by simp [← h]
      -- We proved that x ≠ w*, so x ∈ complex roots of q.
      simp [hxw] at hx ⊢
      exact hx.2
    -- x is a complex root of q, x.im ≠ 0, so q can be factored as follows:
    -- q = (X^2 - (2 * x.re) * X + ‖x‖^2) * t for some t ∈ ℝ[X].
    have ⟨t, hqt⟩ := quadratic_dvd_of_aeval_eq_zero_im_ne_zero q hx0 (hr <| by simp [hp_aroots])
    -- Show that t = v for some non-zero constant v ∈ ℝ.
    have ⟨v, hv, hv0⟩ : ∃ v, t = C v ∧ v ≠ 0:= by
      -- It is enough to show that t = v ∈ ℝ. v ≠ 0 follows from p ≠ 0.
      suffices ∃ v, t = C v by
        have ⟨v, hv⟩ := this
        use v, hv
        contrapose! hpq
        simp [hqt, hv, hpq, hp0]
      use t.coeff 0
      -- It is enough to show that the degree to t is 0.
      apply eq_C_of_degree_eq_zero
      -- The degree of p is 4.
      -- p = (X^2 - (2 * w.re) * X + ‖w‖^2) * (X^2 - (2 * x.re) * X + ‖x‖^2) * t.
      apply_fun degree at hpq
      rw [hqt, degree_mul, degree_mul, degree_eq_natDegree hp0, hdeg] at hpq
      -- The degree of any monic quadratic polynomial is 2.
      have h2 (a b : ℝ) : (X ^ 2 - C a * X + C b).degree = 2 := by compute_degree!
      rw [h2, h2, ← add_assoc] at hpq
      -- We get the equality 4 = 4 + t.degree.
      norm_num at hpq
      nth_rw 1 [← add_zero 4] at hpq
      -- We conclude that t.degree = 0.
      rw [WithBot.add_left_cancel_iff (by simp)] at hpq
      exact hpq.symm
    subst t
    -- We have
    -- p = v * (X^2 - (2 * w.re) * X + ‖w‖^2) * (X^2 - (2 * x.re) * X + ‖x‖^2)
    -- with constant v ≠ 0.
    -- So the complex roots of p are {w, w*, x, x*}
    rw [h, hqt, mul_comm _ (C v), aroots_C_mul _ hv0, h2]
    rfl
  -- Prove that y * z = (w * x)*.
  have hprod' : y * z = starRingEnd ℂ (w * x) := by
    -- It is enough to show that {y, z} = {w*, x*}.
    suffices ({y, z} : Multiset ℂ) = {starRingEnd ℂ w, starRingEnd ℂ x} by
      apply_fun Multiset.prod at this
      simp_all
    -- We have p.aroots ℂ = {w, x, y, z} = {w, w*, x, x*} = {w, x, w*, x*}.
    simp [hp_aroots] at hroots
    -- It follows that {y, z} = {w*, x*}.
    nth_rw 2 [Multiset.cons_swap] at hroots
    simp at hroots
    exact hroots
  -- Now prove that b = 51. It is convenient to prove that b = 51 over ℂ.
  apply Complex.ofReal_inj.mp
  calc
    -- b = the second coefficient of p.
    (b : ℂ) = (p.map (algebraMap ℝ ℂ)).coeff 2 := by simp [hp]
    -- Use Vieta's identitity to show that the second coefficient of p is equal to
    -- the sum of all products u * v with u, v ∈ p.aroots ℂ.
    _ = (w * x + starRingEnd ℂ (w * x)) + (w + x) * starRingEnd ℂ (w + x) := by
        rw [coeff_eq_esymm_roots_of_card]
        rotate_left
        · simp [hdeg, hroots]
        · simp [hdeg]
        -- We proved that p.aroots ℂ = {w, w*, x, x*} so we get:
        -- w * w* + w * x + w * x* + w* * x + w* * x* + x * x*
        --   = (w * x + (w * x)*) + (w + x) * (w + x)*.
        simp [hroots, hdeg, hp1]
        simp [Multiset.esymm, Multiset.powersetCard_one]
        ring
    -- w * x + (w * x)* = 2 * (w * x).re = 2 * (y * z).re,
    -- (w + x) * (w + x)* = ‖w + x‖^2.
    _ = 2 * (y * z).re + (w + x).normSq := by
        rw [Complex.mul_conj, Complex.add_conj, hprod']
        simp
    -- (y * z).re = 13 and ‖w + x‖^2 = 9 + 16, so
    -- b = 2 * 13 + 9 + 16 = 51.
    _ = 51 := by
        simp [hprod, hsum, Complex.normSq]
        norm_num