import Mathlib

/- 7. Given a polynomial $P(x)$, not identically zero. It is known that for all $x$ the identity $(x-2020) \cdot P(x+1)=(x+2021) \cdot P(x)$ holds. How many roots does the equation $P(x)=0$ have? Answer: 4042 -/
theorem algebra_190762 {P : Polynomial ℝ} (hP : P ≠ 0) (h : ∀ x, (x - 2020) * P.eval (x + 1) = (x + 2021) * P.eval x) :
    P.roots.toFinset.card = 4041 := by
  have hinj : (fun (x : ℤ) => (x : ℝ)).Injective := by
    intro x y
    simp only [Int.cast_inj, imp_self]
  -- it is enough to show that all roots of P are integers in [-2020, 2020]
  suffices P.roots.toFinset = (Finset.Icc (-2020 : ℤ) 2020).map ⟨fun (x : ℤ) => (x : ℝ), hinj⟩ by
    simp [this]
  ext x
  simp [hP]
  -- prove that P(x) = 0 and x ≠ 2020 implies that P(x + 1) = 0
  have hsucc {x} (hr : P.eval x = 0) (hx : x ≠ 2020) : P.eval (x + 1) = 0 := by
    -- we have (x - 2020) * P(x + 1) = (x + 2021) * P(x) = 0
    -- x ≠ 2020, so P(x + 1) = 0
    replace h := h x
    rw [hr, mul_zero, mul_eq_zero] at h
    cases' h with h h <;> [skip; assumption]
    contrapose! hx
    linarith
  -- prove that P(x) = 0 and x ≠ -2020 implies that P(x - 1) = 0
  have hpred {x} (hr : P.eval x = 0) (hx : x ≠ -2020) : P.eval (x - 1) = 0 := by
    -- we have 0 = ((x - 1) - 2020) * P((x - 1) + 1) = ((x - 1) + 2021) * P(x - 1)
    -- x ≠ -2020, so P(x - 1) = 0
    replace h := h (x - 1)
    rw [show x - 1 + 1 = x by linarith, hr, mul_zero, eq_comm, mul_eq_zero] at h
    cases' h with h h <;> [skip; assumption]
    contrapose! hx
    linarith
  -- it is easy to show that P(2020) = 0
  have h2020 : P.eval 2020 = 0 := by
    replace h := h 2020
    simp [show (2020 : ℝ) + 2021 ≠ 0 by norm_num] at h
    exact h
  -- show by induction that P(2020 - z) = 0 for any integer z ∈ [0, 4041)
  have hroots (z : ℤ) (hz1 : 0 ≤ z) (hz2 : z < 4041) : P.eval (2020 - z : ℝ) = 0 := by
    lift z to ℕ using hz1
    induction z with
    | zero => simp; exact h2020
    | succ n ih =>
      push_cast
      rw [tsub_add_eq_tsub_tsub]
      apply hpred
      · rify at hz2
        linarith
      apply ih
      omega
  constructor
  · intro h
    -- assume that P(x) = 0 and show that x = z for an integer z ∈ [-2020, 2020]
    -- suppose that x ≠ z for all z ∈ [-2020, 2020]
    contrapose! hP
    -- show that P = 0 in this case
    -- more specifically, show that P has inifinitely many roots
    apply Polynomial.eq_zero_of_infinite_isRoot
    -- consider 2 cases: x > 2020 and x ≤ 2020
    by_cases hx : x > 2020
    -- if x > 2020 then P(x + n) = 0 for all natural numbers n
    -- this follows by induction and from the fact that x + n ≠ 2020 for all n
    · replace hroots (n : ℕ) : P.eval (x + n) = 0 := by
        induction n with
        | zero => simp [h]
        | succ n ih =>
          push_cast
          rw [←add_assoc]
          apply hsucc ih
          linarith
      -- we have P(x + n) = 0 for all natural numbers n, so P has infinitely many roots
      have hs : (fun (n : ℕ) => x + n) '' Set.univ ⊆ {x | P.IsRoot x} := by
        exact Set.image_subset_iff.mpr fun ⦃a⦄ a_1 ↦ hroots a
      apply Set.Infinite.mono hs
      apply Set.Infinite.image _ Set.infinite_univ
      intro x _ y _
      simp
    -- now consider the case x ≤ 2020
    · have hn (n : ℕ) : x - n ≠ -2020 := by
        -- first of all, show that x - n ≠ -2020 for all natural numbers n
        -- suppose that x - n = -2020 and show that x > 2020
        contrapose! hx
        -- x = -2020 + n ∈ ℤ
        have ⟨a, ha⟩ : ∃ (a : ℤ), a = x := by
          use -2020 + n
          rify
          linarith
        rw [←ha]
        -- we know that x ∉ [-2020, 2020] so
        -- -2020 + n ∉ [-2020, 2020] so n > 4040 and it follows that x > 2020
        contrapose! hP
        use a
        simp [ha]
        rify
        exact ⟨by linarith, hP⟩
      -- show by induction that P(x - n) = 0 for all natural numbers n
      replace hroots (n : ℕ) : P.eval (x - n) = 0 := by
        induction n with
        | zero => simp [h]
        | succ n ih =>
          push_cast
          rw [show x - (n + 1) = (x - n) - 1 by linarith]
          apply hpred ih
          exact hn n
      -- we have P(x - n) = 0 for all natural numbers n, so P has infinitely many roots
      have hs : (fun (n : ℕ) => x - n) '' Set.univ ⊆ {x | P.IsRoot x} := by
        exact Set.image_subset_iff.mpr fun ⦃a⦄ a_1 ↦ hroots a
      apply Set.Infinite.mono hs
      apply Set.Infinite.image _ Set.infinite_univ
      intro x _ y _
      simp
  -- verify that any z ∈ [-2020, 2020] is a root of P (we already proved it in hroots)
  · intro ⟨z, ⟨hz1, hz2⟩, hzx⟩
    rw [← hzx, show (z : ℝ) = 2020 - (2020 - z : ℤ) by push_cast; linarith]
    apply hroots <;> linarith