import Mathlib
/- Let $M_0$ be a natural number greater than or equal to 1.
Let $f(0)=2$. For $k \ge 0$, define $f(k+1) = (f(k))^2$ if $k$ is odd, and $f(k+1) = (f(k))^5$ if $k$ is even.
Let $g(0)=4$. For $k \ge 0$, define $g(k+1) = (f(k))^4$ if $k$ is odd, and $g(k+1) = (f(k))^5$ if $k$ is even.
Let $e_f(k)$ denote the exponent of 2 such that $f(k) = 2^{e_f(k)}$, and $e_g(k)$ denote the exponent of 2 such that $g(k) = 2^{e_g(k)}$.
Let $E_{M_0} = \min(e_f(M_0), e_g(M_0))$.
Show that for any natural numbers $m, n$ such that $m \ge M_0$ and $n \ge M_0$, the sum $f(m)+g(n)$ is divisible by $2^{E_{M_0}}$. -/
theorem algebra_634971 (m0 : ℕ) (f g ef eg : ℕ → ℕ) (hf : ∀ k : ℕ, f (k + 1) = if Odd k then f k ^ 2 else f k ^ 5) (hg : ∀ k : ℕ, g (k + 1) = if Odd k then f k ^ 4 else f k ^ 5) (hm0 : m0 ≥ 1) (h1 : f 0 = 2) (h2 : g 0 = 4) (hef : ∀ k : ℕ, f k = 2 ^ ef k) (heg : ∀ k : ℕ, g k = 2 ^ eg k) : ∀ n m : ℕ, n ≥ m0 → m ≥ m0 → 2 ^ (min (ef m0) (eg m0)) ∣ f m + g n:= by
  -- Prove that ef(k+1) = 2*ef(k) if k is odd, 5*ef(k) if k is even
  have h3 : ∀ k : ℕ, ef (k + 1) = if Odd k then 2 * ef k else 5 * ef k:= by
    intro k
    specialize hf k
    rw [hef (k + 1), hef k] at hf
    by_cases hk : Odd k
    .
      -- Case when k is odd: f(k+1) = f(k)^2, so ef(k+1) = 2*ef(k)
      simp [hk] at hf ⊢
      ring_nf at hf ⊢
      replace hf : Nat.log 2 (2 ^ ef (1 + k)) = Nat.log 2 (2 ^ (ef k * 2)):= by rw [hf]
      rw [Nat.log_pow (by omega) _] at hf
      rw [Nat.log_pow (by omega) _] at hf
      exact hf
    .
      -- Case when k is even: f(k+1) = f(k)^5, so ef(k+1) = 5*ef(k)
      simp [hk] at hf ⊢
      ring_nf at hf ⊢
      replace hf : Nat.log 2 (2 ^ ef (1 + k)) = Nat.log 2 (2 ^ (ef k * 5)):= by rw [hf]
      rw [Nat.log_pow (by omega) _] at hf
      rw [Nat.log_pow (by omega) _] at hf
      exact hf
  -- Prove that eg(k+1) = 4*ef(k) if k is odd, 5*ef(k) if k is even
  have h4 : ∀ k : ℕ, eg (k + 1) = if Odd k then 4 * ef k else 5 * ef k:= by
    intro k
    specialize hg k
    rw [heg (k + 1), hef k] at hg
    by_cases hk : Odd k
    .
      -- Case when k is odd: g(k+1) = f(k)^4, so eg(k+1) = 4*ef(k)
      simp [hk] at hg ⊢
      ring_nf at hg ⊢
      replace hg : Nat.log 2 (2 ^ eg (1 + k)) = Nat.log 2 (2 ^ (ef k * 4)):= by rw [hg]
      rw [Nat.log_pow (by omega) _] at hg
      rw [Nat.log_pow (by omega) _] at hg
      exact hg
    .
      -- Case when k is even: g(k+1) = f(k)^5, so eg(k+1) = 5*ef(k)
      simp [hk] at hg ⊢
      ring_nf at hg ⊢
      replace hg : Nat.log 2 (2 ^ eg (1 + k)) = Nat.log 2 (2 ^ (ef k * 5)):= by rw [hg]
      rw [Nat.log_pow (by omega) _] at hg
      rw [Nat.log_pow (by omega) _] at hg
      exact hg
  intro n m hn hm
  rw [hef m, heg n]
  -- Prove that ef is non-decreasing: ef(n+m) ≥ ef(m)
  have h5 : ∀ n m : ℕ, ef (n + m) ≥ ef m:= by
    intro n m
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [show n + 1 + m = n + m + 1 by omega]
      suffices ef (n + m + 1) ≥ ef (n + m) by linarith
      specialize h3 (n + m)
      rw [h3]
      by_cases hn : Odd (n + m)
      all_goals
        simp [hn]
        linarith
  -- Prove that eg is non-decreasing: eg(n+m) ≥ eg(m)
  have h6 : ∀ n m : ℕ, eg (n + m) ≥ eg m:= by
    intro n m
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [show n + 1 + m = n + m + 1 by omega]
      suffices eg (n + m + 1) ≥ eg (n + m) by linarith
      by_cases g : n = 0 ∧ m = 0
      .
        -- Special case when both n and m are 0
        rcases g with ⟨rfl, rfl⟩
        simp
        -- Calculate eg(0) = 2 from g(0) = 4 = 2^2
        replace h2 : eg 0 = 2:= by
          rw [heg 0] at h2
          rw [show 4 = 2 ^ 2 by omega] at h2
          replace h2 : Nat.log 2 (2 ^ eg 0) = Nat.log 2 (2 ^ 2):= by rw [h2]
          rw [Nat.log_pow (by omega) _] at h2
          rw [Nat.log_pow (by omega) _] at h2
          exact h2
        -- Calculate ef(0) = 1 from f(0) = 2 = 2^1
        replace h1 : ef 0 = 1:= by
          rw [show 2 = 2 ^ 1 by omega] at h1
          rw [hef 0] at h1
          replace h1 : Nat.log 2 (2 ^ ef 0) = Nat.log 2 (2 ^ 1):= by rw [h1]
          rw [Nat.log_pow (by omega) _] at h1
          rw [Nat.log_pow (by omega) _] at h1
          exact h1
        specialize h4 0
        simp at h4
        linarith
      .
        -- General case when at least one of n or m is non-zero
        set t:= n + m - 1 with ht
        clear_value t
        rw [show n + m + 1 = t + 1 + 1 by omega]
        rw [show n + m = t + 1 by omega]
        have g3:= h4 (t + 1)
        have g4:= h4 t
        rw [g3, g4]
        by_cases ht1 : Odd t
        .
          -- Case when t is odd: t+1 is even
          have ht2 : ¬Odd (t + 1):= by
            simp
            have ht2 : Odd 1:= by decide
            exact Odd.add_odd ht1 ht2
          simp [ht1, ht2]
          specialize h5 1 t
          rw [show 1 + t = t + 1 by omega] at h5
          linarith
        .
          -- Case when t is even: t+1 is odd
          have ht2 : Odd (t + 1):= by
            simp at ht1
            exact Even.add_one ht1
          simp [ht1, ht2]
          rw [h3 t]
          simp [ht1]
          linarith
  -- Apply the monotonicity results to show ef(m) ≥ ef(m0) and eg(n) ≥ eg(m0)
  specialize h5 (m - m0) m0
  specialize h6 (n - m0) m0
  rw [show m - m0 + m0 = m by omega] at h5
  rw [show n - m0 + m0 = n by omega] at h6
  -- Show that min(ef(m0), eg(m0)) ≤ min(ef(m), eg(n))
  have g1 : min (ef m0) (eg m0) ≤ min (ef m) (eg n):= by exact min_le_min h5 h6
  -- Convert to divisibility: 2^min(ef(m0), eg(m0)) divides 2^min(ef(m), eg(n))
  replace g1 : 2 ^ min (ef m0) (eg m0) ∣ 2 ^ min (ef m) (eg n):= by exact Nat.pow_dvd_pow_iff_le_right'.mpr g1
  -- Show that 2^min(ef(m), eg(n)) divides 2^ef(m)
  have g2 : 2 ^ min (ef m) (eg n) ∣ 2 ^ ef m:= by
    suffices min (ef m) (eg n) ≤ ef m by exact Nat.pow_dvd_pow_iff_le_right'.mpr this
    exact Nat.min_le_left (ef m) (eg n)
  -- Show that 2^min(ef(m), eg(n)) divides 2^eg(n)
  have g3 : 2 ^ min (ef m) (eg n) ∣ 2 ^ eg n:= by
    suffices min (ef m) (eg n) ≤ eg n by exact Nat.pow_dvd_pow_iff_le_right'.mpr this
    exact Nat.min_le_right (ef m) (eg n)
  -- Combine to show 2^min(ef(m), eg(n)) divides 2^ef(m) + 2^eg(n)
  replace g2 : 2 ^ min (ef m) (eg n) ∣ 2 ^ ef m + 2 ^ eg n:= by exact (Nat.dvd_add_iff_right g2).mp g3
  -- Final result: 2^min(ef(m0), eg(m0)) divides f(m) + g(n)
  exact Nat.dvd_trans g1 g2
