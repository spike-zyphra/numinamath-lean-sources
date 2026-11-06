import Mathlib

open Filter Topology Polynomial

-- Given a polynomial p of positive degree.
-- Show that 0 < p(x) for all x iff the leading coefficient of p is positive
-- and p(x) ≠ 0 for all x.
lemma eval_pos_iff_leadingCoeff_pos_and_ne_zero {p : ℝ[X]} (hdeg : 0 < p.degree) :
    (∀ x, 0 < p.eval x) ↔ 0 < p.leadingCoeff ∧ ∀ x, p.eval x ≠ 0 := by
  constructor
  · -- Suppose that 0 < p(x) for all x.
    -- Show that 0 < p.leadingCoeff (p(x) ≠ 0 is trivial).
    intro hx
    refine ⟨?_, fun x => ne_of_gt (hx x)⟩
    -- Assume that p.leadingCoeff ≤ 0 and show that p(a) ≤ 0 for some a.
    contrapose! hx
    -- p.leadingCoeff ≤ 0 and 0 < p.degree imply that
    -- p(x) tends to -∞ as x tends to ∞.
    -- So p(x) ≤ 0 for sufficiently large x.
    have := ((tendsto_atBot_iff_leadingCoeff_nonpos p).mpr ⟨hdeg, hx⟩).eventually_le_atBot 0
    simp at this
    have ⟨a, ha⟩ := this
    use a
    apply ha a (le_refl _)
  · -- Assume that 0 < p.leadingCoeff and p(x) ≠ 0 for all x.
    -- Show that 0 < p(x) for all x.
    intro hx
    -- Suppose that p(x) ≤ 0 for some x and show that p(y) = 0 for some y.
    contrapose! hx
    intro hp
    -- It is enough to show that 0 ≤ p(y) for some y.
    -- This result follows from the intermediate value theorem because p(x) is continuous.
    suffices ∃ y, 0 ≤ p.eval y by
      apply mem_range_of_exists_le_of_exists_ge (by fun_prop) hx this
    -- 0 ≤ p.leadingCoeff and 0 < p.degree imply that
    -- p(x) tends to ∞ as x tends to ∞.
    -- So 0 ≤ p(x) for sufficiently large x.
    have := ((tendsto_atTop_iff_leadingCoeff_nonneg p).mpr ⟨hdeg, le_of_lt hp⟩).eventually_ge_atTop 0
    simp at this
    have ⟨a, ha⟩ := this
    use a
    apply ha a (le_refl _)

-- If the degree of p is positive and 0 < p(x) for all x then
-- p(x) tends to ∞ as x tends to -∞.
lemma tendsto_atBot_atTop_of_eval_pos {p : ℝ[X]} (hdeg : 0 < p.degree)
    (heval : ∀ x, 0 < p.eval x) : Tendsto p.eval atBot atTop := by
  -- It is enough to show that p(-x) tends to ∞ as x tends to ∞.
  suffices Tendsto (p.comp (-X)).eval atTop atTop by
    simpa [Function.comp_def] using this.comp tendsto_neg_atBot_atTop
  -- It is enough to show that the degree of p(-X) is positive and
  -- the leading coefficient of p(-X) is nonnegative.
  rw [tendsto_atTop_iff_leadingCoeff_nonneg]
  -- The degree of p(-X) is positive because the degree of p is positive.
  have hdeg' : 0 < (p.comp (-X)).degree := by
    rw [← natDegree_pos_iff_degree_pos] at hdeg ⊢
    simp [natDegree_comp, hdeg]
  refine ⟨hdeg', ?_⟩
  -- We have 0 < p(-x) for all x, so
  -- eval_pos_iff_leadingCoeff_pos_and_ne_zero implies that
  -- the leading coefficient of p(-X) is positive.
  have heval' x : 0 < (p.comp (-X)).eval x := by simp [heval]
  have := (eval_pos_iff_leadingCoeff_pos_and_ne_zero hdeg').mp heval'
  exact le_of_lt this.1

/- [An odd-degree polynomial has a real root $]$Given a polynomial $P(x)$ and numbers $a_{1}, a_{2}, a_{3}, b_{1}, b_{2}, b_{3}$, such that $a_{1} a_{2} a_{3} \neq 0$. It turns out that $P\left(a_{1} x+b_{1}\right)+P\left(a_{2} x+\right.$ $\left.b_{2}\right)=P\left(a_{3} x+b_{3}\right)$ for any real $x$. Prove that $P(x)$ has at least one real root. -/
theorem algebra_219384 {P : Polynomial ℝ}
    (a b : Fin 3 → ℝ) (ha : a 0 * a 1 * a 2 ≠ 0)
    (h : ∀ x : ℝ, P.eval (a 0 * x + b 0) + P.eval (a 1 * x + b 1) = P.eval (a 2 * x + b 2)) :
    ∃ x : ℝ, P.eval x = 0 := by
  -- Consider two cases: P.natDegree = 0 or 0 < P.natDegree.
  by_cases hdeg : P.natDegree = 0
  · -- If P.natDegree = 0 then P = C c for some constant c.
    rw [natDegree_eq_zero] at hdeg
    have ⟨c, hc⟩ := hdeg
    subst P
    -- The condition h implies that c + c = c, so c = 0.
    simp_all
  -- Assume now that the degree of P is positive.
  replace hdeg : 0 < P.degree := by
    rw [← natDegree_pos_iff_degree_pos]
    omega
  -- Without loss of generality, assume that the leading coefficient of P is positive.
  wlog hP : 0 < P.leadingCoeff generalizing P
  · suffices ∃ x, (-P).eval x = 0 by
      simp only [eval_neg, neg_eq_zero] at this
      exact this
    -- If the leading coefficient of P is negative, then consider -P.
    simp at hP
    apply this
    · intro x
      simp only [Fin.isValue, eval_neg, ← h x, neg_add_rev]
      ac_nf
    · simp [hdeg]
    · simp only [leadingCoeff_neg, Left.neg_pos_iff]
      simp only [lt_iff_le_and_ne, hP, true_and]
      simp [leadingCoeff_eq_zero]
      apply Polynomial.ne_zero_of_degree_gt hdeg
  -- Assume that P(x) ≠ 0 for all x and derive a contradiction.
  by_contra! h0
  -- 0 < P.degree, 0 < P.leadingCoeff, and P(x) ≠ 0 for all x imply that
  -- 0 < P(x) for all x.
  have h_pos := (eval_pos_iff_leadingCoeff_pos_and_ne_zero hdeg).mpr ⟨hP, h0⟩
  -- It is enough to show that there exists x such that P(x) ≤ P(y) for all y.
  suffices ∃ x : ℝ, ∀ y : ℝ, P.eval x ≤ P.eval y by
    have ⟨x, hx⟩ := this
    -- Suppose that P(x) ≤ P(y) for all y.
    -- Show that P(a 0 * x + b 0) + P(a 1 * x + b 1) = P(a 2 * x + b 2) is false.
    contrapose! h
    -- Take y = (x - b 2) / a 2, then a 2 * y + b 2 = x.
    let y := (x - b 2) / a 2
    use y
    have eq : a 2 * y + b 2 = x := by
      have : a 2 ≠ 0 := by
        contrapose! ha
        simp [ha]
      field_simp [y, this]
    rw [eq]
    apply ne_of_gt
    -- We get P(x) < P(a 0 * y + b 0) + P(a 1 * y + b 1) because
    -- P(x) ≤ P(v) for all v and 0 < P(x).
    linarith [hx (a 0 * y + b 0), hx (a 1 * y + b 1), h_pos x]
  -- To show that there exists x such that P(x) ≤ P(y) for all y,
  -- it is enough to show that P(0) ≤ P(x) for all sufficiently
  -- large and sufficiently small x.
  apply Continuous.exists_forall_le' (by fun_prop) 0
  simp only [cocompact_eq_atBot_atTop, eventually_sup]
  constructor
  · -- Show that P(0) ≤ P(x) for sufficiently small x.
    -- It is enough to show that lim P(x) = ∞ as x tends to -∞.
    apply Tendsto.eventually_ge_atTop
    -- This result follows from tendsto_atBot_atTop_of_eval_pos
    -- because 0 < P(x) for all x.
    apply tendsto_atBot_atTop_of_eval_pos hdeg h_pos
  · -- Show that P(0) ≤ P(x) for sufficiently large x.
    -- It is enough to show that lim P(x) = ∞ as x tends to ∞.
    apply Tendsto.eventually_ge_atTop
    -- The result follows from 0 < P.degree and 0 < P.leadingCoeff.
    rw [tendsto_atTop_iff_leadingCoeff_nonneg]
    simp [hdeg, le_of_lt hP]