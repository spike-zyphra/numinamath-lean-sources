import Mathlib

/-Find the maximum number of real roots to a polynomial of the form
\[x^n + x^{n - 1} + \dots + x + 1 = 0,\]where $n$ is a positive integer.-/
theorem algebra_13239:
    IsGreatest {m | ∃(n : ℕ), ∃(f : Polynomial ℝ), 0 < n ∧ f.degree = n ∧ (∀ x, f.eval x = ∑ i ∈ Finset.range (n + 1), x ^ i) ∧ f.roots.toFinset.card = m} 1 := by
  unfold IsGreatest
  constructor
  · -- Prove that 1 is in the set.
    simp
    use 1
    simp
    use ((Polynomial.X : Polynomial ℝ) + 1)
    constructor
    · compute_degree!
    · simp
      have := Polynomial.roots_X_sub_C (-1 : ℝ)
      simp at this
      rw [this]
      simp
  · apply mem_upperBounds.mpr
    simp
    intro m n hn f hf h hm
    rw [hm.symm]
    by_cases hf': Multiset.card f.roots = 0
    . have : f.roots.toFinset.card = 0 := by
        linarith [Multiset.toFinset_card_le f.roots]
      rw [this]
      simp
    apply Nat.le_of_eq
    apply Finset.card_eq_one.mpr
    use -1
    ext x
    simp
    have eq (n : ℕ) : ∀(x : ℝ), (x - 1) * ∑ i ∈ Finset.range (n + 1), x ^ i = x ^ (n + 1) - 1 := by
      intro x
      induction n with
      | zero =>
        simp
      | succ n ih =>
        rw [Finset.range_succ]
        simp
        rw [mul_add, ih]
        ring_nf
    constructor
    . -- If $x^n + x^{n - 1} + \dots + x + 1 = 0,$ then (x - 1)(x^n + x^{n - 1} + \dots + x + 1) = 0, which expands as $x^{n + 1} - 1 = 0.$
      rintro ⟨f_ne_zero, hx⟩
      have hx' : (x - 1) * ∑ i ∈ Finset.range (n + 1), x ^ i = 0 := by
        rw [(h x).symm, hx]
        simp
      rw [eq] at hx'
      -- The only possible real roots of this equation are $x = 1$ and $x = -1.$
      have : x = 1 ∨ x = -1 := by
        have h : x ^ (n + 1) = 1 := by linarith
        obtain (left | right) := (pow_eq_one_iff_of_ne_zero (by linarith: n + 1 ≠ 0)).mp h
        . -- x = 1
          exact Or.inl left
        . -- x = -1 ∧ Even (n + 1)
          exact Or.inr right.1
      -- But $x = 1$ is not a root of the original polynomial.
      obtain (hx' | hx') := this
      . -- x = 1
        have : f.eval x ≠ 0 := by
          rw [h x, hx']
          simp
          linarith
        rw [hx] at this
        absurd this
        rfl
      . exact hx'
    . intro hx
      have : ∃r, r ∈ f.roots := by
        apply Multiset.exists_mem_of_ne_zero
        apply Multiset.card_pos.mp (Nat.zero_lt_of_ne_zero (by assumption))
      obtain ⟨r, hr⟩ := this
      simp at hr
      obtain ⟨f_ne_zero, hr⟩ := hr
      use f_ne_zero
      have hr': (r - 1) * (∑ i ∈ Finset.range (n + 1), r ^ i) = 0 := by
        rw [(h r).symm, hr]
        simp
      rw [eq] at hr'
      -- The only possible real roots of this equation are $x = 1$ and $x = -1.$
      have : r = 1 ∨ r = -1 := by
        have h : r ^ (n + 1) = 1 := by linarith
        obtain (left | right) := (pow_eq_one_iff_of_ne_zero (by linarith: n + 1 ≠ 0)).mp h
        . -- r = 1
          exact Or.inl left
        . -- r = -1 ∧ Even (n + 1)
          exact Or.inr right.1
      obtain (hr' | hr') := this
      . -- r = 1
        have : f.eval r ≠ 0 := by
          rw [h r, hr']
          simp
          linarith
        rw [hr] at this
        absurd this
        rfl
      -- r = -1, which means x = r
      rw [hx, hr'.symm]
      exact hr
