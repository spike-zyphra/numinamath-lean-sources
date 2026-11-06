import Mathlib

open Polynomial

/- Let $P \in \mathbb{R}[X]$ be a non-zero polynomial such that $P \mid P\left(X^{2}+X+1\right)$. Show that the degree of $P$ is even.

Hint: Show that $P$ has no real roots. -/
theorem algebra_161941 {P : Polynomial ℝ} (hP : P ≠ 0) (hP1 : P ∣ P.comp (X ^ 2 + X + 1)) :
    Even (P.degree) := by
  -- P ≠ 0 implies that P.degree = P.natDegree
  rw [degree_eq_natDegree hP]
  -- It is enough to show Even P.natDegree.
  have (n : ℕ) : Even (n : WithBot ℕ) ↔ Even n := by
    simp [Even, WithBot.exists]
    constructor <;> intro ⟨x, h⟩
    · use x
      rw [←WithBot.coe_inj]
      push_cast
      exact h
    · use x
      rw [h]
      rfl
  rw [this]
  -- Consider two cases: Even P.natDegree or Odd P.natDegree.
  cases' Nat.even_or_odd P.natDegree with hp hp
  · exact hp
  -- Suppose that the degree of P is odd.
  -- Then P.natDegree ≠ 0.
  have hP_deg : P.natDegree ≠ 0 := by
    contrapose! hp
    rw [hp]
    exact Nat.not_odd_zero
  -- Prove that P has a root.
  have ⟨x, hx⟩ : ∃ x, x ∈ P.roots.toFinset := by
    simp [hP]
    clear * - hp
    generalize hn : P.natDegree = n
    -- Proof by strong induction on the degree of P.
    induction n using Nat.strongRec generalizing P with
    | ind n ih =>
      -- We have Odd P.natDegree and for all polynomials Q,
      -- Q.natDegree < P.natDegree and Odd Q.natDegree imply that Q has a root.
      -- P.natDegree ≠ 0 since the degree of P is odd.
      have hd : P.natDegree ≠ 0 := by
        contrapose! hp
        rw [hp]
        exact Nat.not_odd_zero
      -- There exists an irreducible factor of P. Call it g.
      have ⟨g, hg, hgp⟩ := exists_irreducible_of_natDegree_ne_zero hd
      -- All irreducible polynomials over a field have positive degree.
      -- All irreducible polynomials over ℝ have degree at most 2.
      -- So the degree of g is either 1 or 2.
      have hg_deg : g.natDegree = 1 ∨ g.natDegree = 2 := by
        suffices 0 < g.natDegree ∧ g.natDegree ≤ 2 by omega
        exact ⟨Irreducible.natDegree_pos hg, Irreducible.natDegree_le_two hg⟩
      cases' hg_deg with h h
      -- Suppose that the degree of g is 1.
      · rw [natDegree_eq_one] at h
        -- Then g = a * X + b for some a ≠ 0 and b.
        have ⟨a, ha0, b, hg⟩ := h
        -- Show that -b / a is a root of P.
        use -b / a
        -- It is enough to show that -b / a is a root of g since g ∣ P.
        apply eval_eq_zero_of_dvd_of_eval_eq_zero hgp
        simp [← hg]
        field_simp
        ring
      -- Suppose that the degree of g is 2.
      -- We have P = g * q for some q ∈ ℝ[X].
      · have ⟨q, hq⟩ := hgp
        -- We get q.natDegree + 2 = P.natDegree.
        have hq_deg : q.natDegree + 2 = P.natDegree := by
          apply_fun Polynomial.natDegree at hq
          rw [natDegree_mul, h, add_comm] at hq
          · exact hq.symm
          · contrapose! hq
            simp [hq, hd]
          · contrapose! hq
            simp [hq, hd]
        -- The degree of q must be odd (since the degree of P is odd).
        have hq_deg' : Odd q.natDegree := by
          apply_fun Odd at hq_deg
          simp_all [Nat.odd_add]
        -- Apply the induction hypothesis to q and find a root of q.
        have ⟨x, hx⟩ := @ih q.natDegree (by omega) q hq_deg' rfl
        -- P = g * q, so any root of q is also a root of P.
        use x
        simp [hq, hx]
  -- Roots of P are non-empty, so there exists the maximum root of P.
  -- Let a be the maximum root of P.
  have ⟨a, ha⟩ := Finset.max_of_mem hx
  have has := Finset.mem_of_max ha
  -- Show that a^2 + a + 1 is also a root of P.
  have h : a ^ 2 + a + 1 ∈ P.roots.toFinset := by
    -- It is enough to show that a is a root of P(X^2 + X + 1) since
    -- P(X^2 + X + 1) evaluated at a is equal to P(a^2 + a + 1).
    suffices a ∈ (P.comp (X ^ 2 + X + 1)).roots by simp_all
    -- It is enough to show that all roots of P are also roots of P(X^2 + X + 1).
    suffices P.roots ≤ (P.comp (X ^ 2 + X + 1)).roots by
      apply Multiset.mem_of_le this
      rw [← Multiset.mem_toFinset]
      exact has
    -- We have P ∣ P(X^2 + X + 1) so it is enough to show that P(X^2 + X + 1) ≠ 0.
    apply roots.le_of_dvd _ hP1
    apply ne_zero_of_natDegree_gt (n := 0)
    -- The degree of P(X^2 + X + 1) is P.natDegree * (X^2 + X + 1).natDegree > 0.
    simp [natDegree_comp]
    refine ⟨by omega, ?_⟩
    suffices (X ^ 2 + X + 1 : ℝ[X]).natDegree = 2 by simp [this]
    compute_degree!
  -- a is the maximum root of P, so any root of P <= a.
  -- In particular, a^2 + a + 1 ≤ a.
  have := Finset.le_max_of_eq h ha
  -- One the other hand, we have a^2 + a + 1 > a for any a, a contradiction.
  -- So the degree of P must be even.
  contrapose! this
  nlinarith