import Mathlib
/- Let $a,b,c$ be real numbers such that $ab\not= 0$ and $c>0$. Let $(a_{n})_{n\geq 1}$ be the sequence of real numbers defined by: $a_{1}=a, a_{2}=b$ and
\[a_{n+1}=\frac{a_{n}^{2}+c}{a_{n-1}}\]
for all $n\geq 2$.
Show that all the terms of the sequence are integer numbers if and only if the numbers $a,b$ and $\frac{a^{2}+b^{2}+c}{ab}$ are integers. -/
theorem number_theory_61392 (a b c : ℝ) (x : ℕ → ℝ) (h1 : a * b ≠ 0) (h2 : c > 0) (hx1 : x 0 = a) (hx2 : x 1 = b) (hxn : ∀ n : ℕ, x (n + 2) * x n = x (n + 1) ^ 2 + c) : (∀ n : ℕ, ∃ k : ℤ, x n = k) ↔ (∃ k1 k2 k3 : ℤ, a = k1 ∧ b = k2 ∧ (a ^ 2 + b ^ 2 + c) / (a * b) = k3):= by
  -- First, prove that all terms of the sequence are non-zero
  have h3 : ∀ n : ℕ, x n ≠ 0:= by
    intro n
    replace hxn:= hxn n
    by_contra H
    simp [H] at hxn
    linarith [sq_nonneg (x (n + 1))]

  -- Prove that the ratio (x_{n+2} + x_n) / x_{n+1} is constant for all n
  have h4 : ∀ n : ℕ, (x (n + 2) + x n) / x (n + 1) = (x 2 + x 0) / x 1:= by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [show n + 1 + 2 = n + 3 by omega]
      rw [show n + 1 + 1 = n + 2 by omega]
      rw [←ih]
      have g1:= h3 (n + 1)
      have g2:= h3 (n + 2)
      field_simp
      have g3:= hxn n
      have g4:= hxn (n + 1)
      rw [show n + 1 + 2 = n + 3 by omega] at g4
      rw [show n + 1 + 1 = n + 2 by omega] at g4
      linarith

  -- Calculate x_2 using the recurrence relation
  have h5:= hxn 0
  simp at h5
  rw [hx1, hx2] at h5
  replace h5 : x 2 = (b ^ 2 + c) / a:= by
    simp at h1
    rcases h1 with ⟨ha, -⟩
    field_simp
    linarith

  -- Express the constant ratio in terms of a, b, c
  have h6 : (x 2 + x 0) / x 1 = (a ^ 2 + b ^ 2 + c) / (a * b):= by
    rw [hx1, hx2, h5]
    simp at h1
    rcases h1 with ⟨ha, hb⟩
    field_simp
    ring_nf

  -- Start the main proof with constructor for the biconditional
  constructor
  .
    -- Forward direction: if all terms are integers, then a, b, and the ratio are integers
    intro h
    -- Prove that c must be an integer
    have hcin : ∃ c1 : ℕ, c1 = c:= by
      replace hxn:= hxn 0
      simp at hxn
      have g1:= h 0
      have g2:= h 1
      have g3:= h 2
      rcases g1 with ⟨k1, hk1⟩
      rcases g2 with ⟨k2, hk2⟩
      rcases g3 with ⟨k3, hk3⟩
      rw [hk1, hk2, hk3] at hxn
      replace hxn : c = k3 * k1 - k2 ^ 2:= by linarith
      use (k3 * k1 - k2 ^ 2).natAbs
      rw [hxn]
      set s:= k3 * k1 - k2 ^ 2 with hs
      clear_value s
      rify at hs
      rw [←hs]
      rw [show (↑s.natAbs : ℝ) = (↑(↑s.natAbs : ℤ) : ℝ) by rfl]
      simp
      rify
      linarith

    -- Extract integer values for the first three terms
    have g1:= h 0
    have g2:= h 1
    have g3:= h 2
    rcases g1 with ⟨k1, hk1⟩
    rcases g2 with ⟨k2, hk2⟩
    rcases g3 with ⟨k3, hk3⟩
    rw [hx1] at hk1
    rw [hx2] at hk2

    -- Prove that the ratio must be rational
    replace h4 : ∃ k : ℤ, k = (x 2 + x 0) / x 1:= by
      set t:= (x 2 + x 0) / x 1 with ht
      clear_value t
      have h4 : ∃ k : ℚ, t = k:= by
        use (k1 + k3) / k2
        replace h3:= h3 1
        rw [hx2] at h3
        simp
        rw [ht, hk3, hx2, hx1, hk1, hk2]
        ring_nf
      rcases h4 with ⟨r, hr⟩
      rw [show r = r.num / r.den by exact Eq.symm (Rat.num_div_den r)] at hr
      set p:= r.num with hp
      set q:= r.den with hq
      clear_value p q
      simp at hr
      have hqpos : q > 0:= by subst q ; positivity
      by_cases hq1 : q = 1
      .
        -- If denominator is 1, the ratio is already an integer
        rw [hq1] at hr
        simp at hr
        use p
        rw [hr]
      .
        -- If denominator is greater than 1, derive a contradiction
        replace hqpos : q ≥ 2:= by omega
        clear hq1
        replace h4 : ∀ n : ℕ, x (n + 2) + x n = t * x (n + 1):= by
          intro n
          replace h4:= h4 n
          replace h3:= h3 (n + 1)
          field_simp at h4
          linarith

        -- Prove that t^m * x_n is an integer for all m, n with n ≥ m
        have g : ∀ m : ℕ, ∀ n : ℕ, n ≥ m → (∃ k : ℤ, t ^ m * x n = k):= by
          intro m
          induction m with
          | zero =>
            intro n _
            simp
            exact h n
          | succ m ih =>
            intro n hn
            replace h4:= h4 (n - 1)
            rw [show n - 1 + 1 = n by omega] at h4
            rw [show n - 1 + 2 = n + 1 by omega] at h4
            have g1:= ih (n - 1) (by omega)
            have g2:= ih (n + 1) (by omega)
            rcases g1 with ⟨w1, hw1⟩
            rcases g2 with ⟨w2, hw2⟩
            replace h4 : t ^ m * (x (n + 1) + x (n - 1)) = t ^ m * (t * x n):= by rw [h4]
            rw [show t ^ m * (t * x n) = t ^ (m + 1) * x n by ring] at h4
            use w1 + w2
            simp
            linarith

        rcases hcin with ⟨c1, hc1⟩
        -- Prove that q^n divides c for all n
        replace g : ∀ n : ℕ, q ^ n ∣ c1:= by
          intro n
          replace g : ∀ n : ℕ, ∃ k : ℤ, x n = q ^ n * k:= by
            intro n
            replace g:= g n n (by omega)
            rcases g with ⟨w, hw⟩
            replace h:= h n
            rcases h with ⟨s, hs⟩
            rw [hs] at hw ⊢
            replace hw : (q : ℤ) ^ n ∣ p ^ n * s:= by
              rw [hr] at hw
              ring_nf at hw
              field_simp at hw
              use w
              rify
              linarith only [hw]
            have g1 : Nat.Coprime (p.natAbs) q:= by
              rw [hp, hq]
              exact r.reduced
            replace g1 : IsCoprime p (q : ℤ):= by exact Int.isCoprime_iff_gcd_eq_one.mpr g1
            replace g1 : IsCoprime (q : ℤ) p:= by exact id (IsCoprime.symm g1)
            replace g1 : IsCoprime ((q : ℤ) ^ n) (p ^ n):= by exact IsCoprime.pow g1
            replace hw : (q : ℤ) ^ n ∣ s:= by exact IsCoprime.dvd_of_dvd_mul_left g1 hw
            rcases hw with ⟨w1, hw1⟩
            use w1
            rify at hw1
            exact hw1
          replace hxn:= hxn n
          have g1:= g n
          have g2:= g (n + 1)
          have g3:= g (n + 2)
          rcases g1 with ⟨w1, hw1⟩
          rcases g2 with ⟨w2, hw2⟩
          rcases g3 with ⟨w3, hw3⟩
          rw [hw1, hw2, hw3, ←hc1] at hxn
          zify
          use (w1 * w3 * q ^ (n + 2) - w2 ^ 2 * q ^ (n + 2))
          rify
          ring_nf at hxn ⊢
          linarith only [hxn]

        -- Prove that c must be at least n for all n, which is impossible
        replace g : ∀ n : ℕ, c1 ≥ n:= by
          intro n
          replace hc1 : c1 ≠ 0:= by
            by_contra H
            rw [H] at hc1
            simp at hc1
            linarith
          replace g:= g n
          apply Nat.le_of_dvd (by omega) at g
          have g1 : q ^ n ≥ 2 ^ n:= by exact Nat.pow_le_pow_of_le_left hqpos n
          have g2 : ∀ n : ℕ, 2 ^ n ≥ n + 1:= by
            intro n
            induction n with
            | zero =>
              simp
            | succ n ih =>
              ring_nf
              linarith
          replace g2:= g2 n
          linarith
        replace g:= g (c1 + 1)
        linarith

    -- Construct the required integers for the conclusion
    rcases h4 with ⟨k4, h4⟩
    use k1, k2, k4
    refine ⟨hk1, hk2, ?_⟩
    rw [h4, h6]
  .
    -- Reverse direction: if a, b, and the ratio are integers, then all terms are integers
    intro h
    rcases h with ⟨k1, k2, k3, ha, hb, hc⟩

    -- Express the recurrence relation in terms of the constant ratio
    replace h4 : ∀ n : ℕ, x (n + 2) = k3 * x (n + 1) - x n:= by
      intro n
      replace h4:= h4 n
      rw [h6, hc] at h4
      have g : x (n + 1) ≠ 0:= by
        by_contra H
        replace hxn:= hxn (n + 1)
        simp [H] at hxn
        linarith [sq_nonneg (x (n + 1 + 1))]
      field_simp at h4
      linarith

    -- Prove by induction that all terms are integers
    have h7 : ∀ n : ℕ, (∃ k1 : ℤ, x n = k1) ∧ (∃ k2 : ℤ, x (n + 1) = k2):= by
      intro n
      induction n with
      | zero =>
        simp [hx1, hx2]
        refine ⟨?_, ?_⟩
        use k1
        use k2
      | succ n ih =>
        rcases ih with ⟨⟨k1, hk1⟩, ⟨k2, hk2⟩⟩
        refine ⟨?_, ?_⟩
        exact ⟨k2, hk2⟩
        rw [show n + 1 + 1 = n + 2 by omega]
        use k3 * k2 - k1
        simp
        replace h4:= h4 n
        rw [hk2, hk1] at h4
        exact h4

    -- Extract the integer property for any term
    intro n
    replace h7:= h7 n
    exact h7.1
