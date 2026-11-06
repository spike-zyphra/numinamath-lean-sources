import Mathlib

open Polynomial

/- Let P(x) be a nonzero polynomial such that (x−1)P(x+1)=(x+2)P(x) for every real x, and P(2)^2=P(3).
Then P(7/2)=m/n​, where m and n are relatively prime positive integers. Find m+n. -/
theorem algebra_34454 {P : ℝ[X]} (hp0 : P ≠ 0) (hp : ∀ x : ℝ, (x - 1) * P.eval (x + 1) = (x + 2) * P.eval x) (hp2 : P.eval 2 ^ 2 = P.eval 3) :
    ∀ m n : ℕ, m > 0 ∧ n > 0 ∧ Nat.Coprime m n ∧ P.eval (7 / 2) = m / n → m + n = 109 := by
  -- show that P = Q * (X - 1) * X * (X + 1) for some non-zero polynomial Q
  have ⟨Q, hq0, hp_eq⟩ : ∃ Q ≠ 0, P = Q * (X - 1) * X * (X + 1) := by
    -- 1 is a root of P since 0 = 0 * P(2) = 3 * P(1)
    have hr1 : P.IsRoot 1 := by
      rw [IsRoot.def]
      linarith [hp 1]
    -- 0 is a root of P since -1 * P(1) = 2 * P(0) and P(1) = 0
    have hr0 : P.IsRoot 0 := by
      rw [IsRoot.def] at hr1 ⊢
      have := hp 0
      norm_num at this
      linarith
    -- -1 is a root of P since -2 * P(0) = 1 * P(-1) and P(0) = 0
    have hr2 : P.IsRoot (-1) := by
      rw [IsRoot.def] at hr0 ⊢
      have := hp (-1)
      norm_num at this
      linarith
    -- if r is a root of a polynomial P ≠ 0 then P = (X - r) * Q for some Q ≠ 0
    have root_factor {P : ℝ[X]} (hp0 : P ≠ 0) r (hr : P.IsRoot r) : ∃ Q ≠ 0, P = (X - C r) * Q := by
      rw [← Polynomial.mul_div_eq_iff_isRoot] at hr
      use P / (X - C r)
      simp only [ne_eq, hr, and_true]
      contrapose! hr
      simp [hr]
      exact fun h => hp0 $ symm h
    -- apply the above lemma 3 times and obtain P = Q * (X - 1) * X * (X + 1) with Q ≠ 0
    have ⟨Q1, hq1_0, hq1_eq⟩ := root_factor hp0 (-1) hr2
    have hqr0 : Q1.IsRoot 0 := by
      rw [IsRoot.def] at hr0 ⊢
      apply_fun eval 0 at hq1_eq
      simp at hq1_eq
      linarith
    have ⟨Q2, hq2_0, hq2_eq⟩ := root_factor hq1_0 0 hqr0
    have hqr1 : Q2.IsRoot 1 := by
      rw [IsRoot.def] at hr1 ⊢
      apply_fun eval 1 at hq1_eq
      simp [hq2_eq] at hq1_eq
      linarith
    have ⟨Q, hq0, hq_eq⟩ := root_factor hq2_0 1 hqr1
    use Q, hq0
    simp [hq1_eq, hq2_eq, hq_eq]
    ring
  -- we have:
  -- (x - 1) * P(x + 1) = (x - 1) * Q(x + 1) * x * (x + 1) * (x + 2)
  --                    = (x + 2) * P(x)
  --                    = (x + 2) * Q(x) * (x - 1) * x * (x + 1)
  -- Hence, if x > 1 then Q(x + 1) = Q(x)
  have hqeval : ∀ x > 1, Q.eval (x + 1) = Q.eval x := by
    intro x hx
    apply mul_left_cancel₀ (show x - 1 ≠ 0 by linarith)
    apply mul_left_cancel₀ (show x ≠ 0 by linarith)
    apply mul_left_cancel₀ (show x + 1 ≠ 0 by linarith)
    apply mul_left_cancel₀ (show x + 2 ≠ 0 by linarith)
    specialize hp x
    simp [hp_eq] at hp
    ring_nf at hp
    ring_nf
    exact hp
  -- show that Q(x + 1) = Q(x) for all x > 1 implies that Q is a constant polynomial
  have ⟨c, hqc⟩ : ∃ c : ℝ, Q = C c := by
    -- define R(x) = Q(x) - Q(2)
    set R := Q - C (Q.eval 2) with hr_eq
    -- consider 2 cases: R = 0 and R ≠ 0
    by_cases h : R = 0
    -- if R = 0 then Q(x) = Q(2), a constant polynomial
    · use Q.eval 2
      rw [←sub_eq_zero]
      simp [←hr_eq, h]
    -- if R ≠ 0 then we can find r ∈ ℝ such that any root y of R is bounded by r: y ≤ r
    · have ⟨r, hr⟩ := Polynomial.exists_max_root R h
      -- it is enough to show that n + 2 is a root of R for any n ∈ ℕ
      suffices hqn : ∀ n : ℕ, R.IsRoot (n + 2) by
        -- find n ∈ ℕ such that r ≤ n
        have ⟨n, hn⟩ := exists_nat_ge r
        -- n + 2 is a root of R and hence n + 2 ≤ r
        have := hr _ (hqn n)
        -- we have: n + 2 ≤ r ≤ n, a contradiction
        linarith
      -- now show that n + 2 is a root of R for any n ∈ ℕ
      intro n
      rw [IsRoot.def]
      -- proof by induction
      induction n with
      | zero => simp [hr_eq]
      | succ n ih =>
        -- we have
        -- R(n + 3) = Q(n + 3) - Q(2) (by the definition of R)
        --          = Q(n + 2) - Q(2) (because Q(x + 1) = Q(x) for any x > 1)
        --          = R(n + 2)        (by the definition of R)
        --          = 0               (by induction hypothesis)
        simp [hr_eq, show (n : ℕ) + (1 : ℝ) + 2 = ((n : ℝ) + 2) + 1 by ring] at ih ⊢
        rw [hqeval _ (by linarith), ih]
  -- we have P = c * (X - 1) * X * (X + 1) for some constant c
  -- we compute P(2)^2 = c^2 * 36 = P(3) = c * 24
  -- hence, c = 0 or c = 2 / 3
  -- c = 0 is impossible since P ≠ 0 and we obtain c = 2 / 3
  have hc : c = 2 / 3 := by
    have hc0 : c ≠ 0 := by
      contrapose! hp0
      simp [hp_eq, hqc, hp0]
    simp [hp_eq, hqc] at hp2
    ring_nf at hp2
    rw [pow_two, mul_assoc] at hp2
    apply mul_left_cancel₀ hc0 at hp2
    linarith
  -- it is left to show that P(7 / 2) = 105 / 4
  intro m n
  simp [hp_eq, hqc, hc]
  norm_num
  intro hm hn hmn h
  field_simp at h
  suffices m = 105 ∧ n = 4 by omega
  zify
  apply Rat.div_int_inj <;> norm_cast
  rw [NNRat.divNat_inj (by omega) (by norm_num)]
  rify
  rw [h]