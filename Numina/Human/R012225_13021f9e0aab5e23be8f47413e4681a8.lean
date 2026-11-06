import Mathlib

open Polynomial

/- Find all polynomials $P$ such that
$$
P\left(x^{2}-2 x\right)=(P(x-2))^{2}
$$
 -/
theorem algebra_193567 {P : ℝ[X]} :
    (∀ x, P.eval (x^2 - 2 * x) = (P.eval (x - 2))^2) ↔ P = 0 ∨ ∃ n, P = (X + 1)^n := by
  symm
  constructor
  -- Show that P = 0 or P = (X + 1)^n implies that P(x^2 - 2 * x) = P(x - 2)^2 for all x.
  · intro h
    rcases h with h | ⟨n, h⟩
    · simp [h]
    · simp [h]
      intro x
      rw [show x ^ 2 - 2 * x + 1 = (x - 1)^2 by ring, ← pow_mul, ← pow_mul]
      ring_nf
  -- Assume that P(x^2 - 2 * x) = P(x - 2)^2 for all x and show that
  -- P = 0 or P = (X + 1)^n for some n.
  intro hp
  -- Consider two cases: P = 0 and P ≠ 0.
  by_cases hp0 : P = 0
  · tauto
  -- Suppose that P ≠ 0 and show that P = (X + 1)^n for some n.
  right
  -- Define Q = P(X - 1).
  set Q : ℝ[X] := P.comp (X - 1)
  -- It is enough to show that Q = X^n for some n.
  suffices ∃ n, Q = X ^ n by
    have ⟨n, hq⟩ := this
    use n
    have hpq : P = Q.comp (X + 1) := by
      apply Polynomial.funext
      simp [Q]
    simp [hpq, hq]
  -- P(x^2 - 2 * x) = P(x - 2)^2 for all x implies that Q^2 = Q(X^2).
  have hq : Q ^ 2 = Q.comp (X ^ 2) := by
    apply Polynomial.funext
    intro x
    simp [Q]
    have hp := hp (x + 1)
    rw [show x + 1 - 2 = x - 1 by ring] at hp
    rw [← hp]
    ring_nf
  -- We have Q ≠ 0 (since P ≠ 0).
  have hq0 : Q ≠ 0 := by
    contrapose! hp0
    have hpq : P = Q.comp (X + 1) := by
      apply Polynomial.funext
      simp [Q]
    simp [hpq, hp0]
  -- Let n be the degree of Q and prove that Q = X ^ n
  set n := Q.natDegree with hn
  use n
  -- Show that the leading coefficient (call it a0) of Q is 1
  have hq_leading : Q.leadingCoeff = 1 := by
    -- The leading coefficient of Q ^ 2 is a0 ^ 2
    have hq1 : (Q ^ 2).leadingCoeff = Q.leadingCoeff ^ 2 := by simp only [leadingCoeff_pow]
    -- The leading coefficient of Q(X ^ 2) is a0
    have hq2 : (Q.comp (X ^ 2)).leadingCoeff = Q.leadingCoeff := by simp [leadingCoeff_comp]
    -- We get a0 * (a0 - 1) = 0
    replace eq : Q.leadingCoeff * (Q.leadingCoeff - 1) = 0 := by
      rw [hq] at hq1
      linear_combination hq2 - hq1
    -- So a0 = 0 or a0 = 1.
    -- If a0 = 0 then Q = 0, a contradiction, so a0 = 1.
    rw [mul_eq_zero] at eq
    cases' eq with h h
    · rw [leadingCoeff_eq_zero] at h; contradiction
    · linarith
  -- Consider two cases: n = 0 and 0 < n.
  by_cases hn0 : n = 0
  · rw [hn0, pow_zero]
    -- If n = 0 then Q.leadingCoeff = 1 implies that Q = 1
    rw [← Monic.natDegree_eq_zero hq_leading]
    exact hn0
  -- Let g be the polynomial Q as a polynomial over ℂ.
  set g := Q.map Complex.ofRealHom
  -- g satisfies the same polynomial equality as Q.
  have hg : g ^ 2 = g.comp (X ^ 2) := by
    apply_fun Polynomial.map Complex.ofRealHom at hq
    simp at hq
    simp [g, hq, Polynomial.map_comp]
  have hg_eval z : eval z g ^ 2 = eval (z ^ 2) g := by
    apply_fun Polynomial.eval z at hg
    simp at hg
    exact hg
  -- The degree of g is n.
  have hg_deg : g.natDegree = n := by simp only [natDegree_map, g]
  -- The leading coefficient of g is 1.
  have hg_leading : g.leadingCoeff = 1 := by simp [g, hq_leading]
  -- g ≠ 0.
  have hg0 : g ≠ 0 := by simp [g, hq0]
  -- Show that 0 is the only root of g.
  have hg_roots : g.roots = n • {0} := by
    -- g has exactly n roots (because g ∈ ℂ[X] and the degree of g is n).
    have n_eq : n = g.roots.card := by
      symm
      rw [←hg_deg, ←Polynomial.splits_iff_card_roots]
      exact IsAlgClosed.splits g
    rw [Multiset.nsmul_singleton, n_eq]
    apply Multiset.eq_replicate_of_mem
    -- It is enough to show that z ∈ g.roots implies that z = 0.
    simp_rw [Polynomial.mem_roots hg0]
    intro z hz
    -- Suppose that z ∈ g.roots and z ≠ 0.
    -- Show that g = 0 in this case.
    contrapose! hg0
    -- We have g(u ^ 2 ^ n) = g(u) ^ (2 ^ n) for any natural n and complex u.
    have hzn z n : g.eval (z ^ 2 ^ n) = (g.eval z) ^ (2 ^ n) := by
      induction n with
      | zero => simp only [pow_zero, pow_one]
      | succ n ih => rw [Nat.pow_add, pow_mul, pow_one, ←hg_eval, ih, pow_mul]
    -- Show that roots of X ^ (2 ^ n) - z are also roots of g
    -- and that X ^ (2 ^ n) - z has more than n roots.
    -- It follows that g has more than n roots, so g = 0.
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ (nthRoots (2 ^ n) z).toFinset
    · simp
      -- If v is a root of X ^ (2 ^ n) - z then
      -- v ^ (2 ^ n) = z and we have
      -- 0 = g(z) = g(v ^ (2 ^ n)) = g(v) ^ (2 ^ n).
      intro v eq
      replace hzn := hzn v n
      rw [eq, hz, eq_comm] at hzn
      rw [pow_eq_zero_iff (by norm_num)] at hzn
      exact hzn
    · have hp := Complex.isPrimitiveRoot_exp (2 ^ n) (by norm_num)
      have : (nthRoots (2 ^ n) z).Nodup := IsPrimitiveRoot.nthRoots_nodup hp hg0
      -- Show that there are exactly 2 ^ n roots of X ^ (2 ^ n) - z.;
      rw [Multiset.toFinset_card_of_nodup this]
      have : ∃ v, v ^ (2 ^ n) = z := by
        use z ^ ((↑((2 : ℕ) ^ n) : Complex)⁻¹)
        rw [Complex.cpow_nat_inv_pow]
        norm_num
      simp [IsPrimitiveRoot.card_nthRoots hp, this, hg_deg]
      clear * -
      -- It is left to show that n < 2 ^ n for all n.
      induction n with
      | zero => norm_num
      | succ n ih =>
        rw [pow_add, pow_one, mul_two]
        exact add_lt_add_of_lt_of_le ih (by omega)
  -- We can write g = ∏ a ∈ g.roots, (X - a) = X ^ n (since g.roots = n • {0}).
  have hg_eq := Polynomial.eq_prod_roots_of_monic_of_splits_id hg_leading (IsAlgClosed.splits g)
  simp [hg_roots, Multiset.map_nsmul, Multiset.prod_nsmul] at hg_eq
  -- It is left to show that Q = X ^ n.
  -- Show that Q(x) = (X ^ n)(x) for all real x.
  apply Polynomial.funext
  intro x
  rw [←Complex.ofReal_inj]
  -- We have Q(x) = g(x) for all real x.
  have hgf x : Q.eval x = g.eval (x : ℂ) := by
    simp_rw [g, eval_map, eval_eq_sum, eval₂_def, sum_def]
    simp
  -- g(x) = x ^ n so Q(x) = x ^ n for all real x and it follows that Q = X ^ n.
  simp_all only [eval_pow, eval_X, Complex.ofReal_pow]