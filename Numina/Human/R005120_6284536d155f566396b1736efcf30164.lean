import Mathlib
/- Zij $n$ een positief geheel getal. Bewijs dat de getallen

$$
1^{1}, 3^{3}, 5^{5}, \ldots,\left(2^{n}-1\right)^{2^{n}-1}
$$

in verschillende restklassen zitten modulo $2^{n}$. -/
theorem algebra_605622 (f : ℕ → ℕ) (hf : f = fun n => n ^ n) (n : ℕ) (hn : n > 0) : ∀ i < 2 ^ (n - 1), ∀ j < 2 ^ (n - 1),  i ≠ j → ¬(f (2 * i + 1) ≡ f (2 * j + 1) [MOD 2 ^ n]):= by
  -- Set m = n - 1 and clear its value for induction
  set m:= n - 1 with hm
  clear_value m
  replace hm : n = m + 1:= by omega
  subst n
  clear hn
  -- Induction on m
  induction m with
  | zero =>
    -- Base case: m = 0
    simp
  | succ m ih =>
    -- Inductive step: m = m + 1
    intro i hi j hj hij
    by_contra H
    -- Key lemma: for odd k, f(k + 2^(m+1)) ≡ f(k) + 2^(m+1) [MOD 2^(m+1+1)]
    have h1 : ∀ k : ℕ, Odd k → f (k + 2 ^ (m + 1)) ≡ f k + 2 ^ (m + 1) [MOD 2 ^ (m + 1 + 1)]:= by
      intro k hk
      simp [hf]
      -- Prove by induction that (k + 2^(m+1))^(n+1) ≡ k^(n+1) + (n+1)*2^(m+1)*k^n [MOD 2^(m+1+1)]
      have h1 : ∀ n : ℕ, (k + 2 ^ (m + 1)) ^ (n + 1) ≡ k ^ (n + 1) + (n + 1) * 2 ^ (m + 1) * k ^ n [MOD 2 ^ (m + 1 + 1)]:= by
        intro n
        induction n with
        | zero =>
          -- Base case: n = 0
          simp
          rfl
        | succ n ih =>
          -- Inductive step: expand (k + 2^(m+1))^(n+2)
          rw [show (k + 2 ^ (m + 1)) ^ (n + 1 + 1) = (k + 2 ^ (m + 1)) ^ (n + 1) * (k + 2 ^ (m + 1)) by ring]
          replace ih:= Nat.ModEq.mul_right (k + 2 ^ (m + 1)) ih
          -- Show the expanded form is congruent to the desired expression
          suffices (k ^ (n + 1) + (n + 1) * 2 ^ (m + 1) * k ^ n) * (k + 2 ^ (m + 1)) ≡ k ^ (n + 1 + 1) + (n + 1 + 1) * 2 ^ (m + 1) * k ^ (n + 1) + 0 [MOD 2 ^ (m + 1 + 1)] by exact Nat.ModEq.trans ih this
          -- Expand the left side
          rw [show (k ^ (n + 1) + (n + 1) * 2 ^ (m + 1) * k ^ n) * (k + 2 ^ (m + 1)) = k ^ (n + 2) + (n + 2) * 2 ^ (m + 1) * k ^ (n + 1) + (n + 1) * k ^ n * 2 ^ (2 * m + 2) by ring_nf]
          rw [show n + 1 + 1 = n + 2 by omega]
          rw [show m + 1 + 1 = m + 2 by omega]
          -- Show the extra term is divisible by 2^(m+2)
          suffices (n + 1) * k ^ n * 2 ^ (2 * m + 2) ≡ 0 [MOD 2 ^ (m + 2)] by exact Nat.ModEq.add_left (k ^ (n + 2) + (n + 2) * 2 ^ (m + 1) * k ^ (n + 1)) this
          suffices 2 ^ (m + 2) ∣ (n + 1) * k ^ n * 2 ^ (2 * m + 2) by exact Nat.modEq_zero_iff_dvd.mpr this
          use (n + 1) * k ^ n * 2 ^ m
          ring_nf
      -- Apply the lemma with n = k + 2^(m+1) - 1
      replace h1:= h1 (k + 2 ^ (m + 1) - 1)
      have g : 2 ^ (m + 1) > 0:= by positivity
      rw [show k + 2 ^ (m + 1) - 1 + 1 = k + 2 ^ (m + 1) by omega] at h1
      -- Expand the expression
      rw [show (k + 2 ^ (m + 1)) * 2 ^ (m + 1) * k ^ (k + 2 ^ (m + 1) - 1) = 2 ^ (2 * m + 2) * k ^ (k + 2 ^ (m + 1) - 1) + 2 ^ (m + 1) * k ^ (k + 2 ^ (m + 1) - 1 + 1) by ring_nf] at h1
      rw [show k + 2 ^ (m + 1) - 1 + 1 = k + 2 ^ (m + 1) by omega] at h1
      rw [show k ^ (k + 2 ^ (m + 1)) + (2 ^ (2 * m + 2) * k ^ (k + 2 ^ (m + 1) - 1) + 2 ^ (m + 1) * k ^ (k + 2 ^ (m + 1))) = k ^ (k + 2 ^ (m + 1)) + 2 ^ (m + 1) * k ^ (k + 2 ^ (m + 1)) + 2 ^ (2 * m + 2) * k ^ (k + 2 ^ (m + 1) - 1) by ring] at h1
      -- Show the higher power term is divisible by 2^(m+1+1)
      have h2 : 2 ^ (2 * m + 2) * k ^ (k + 2 ^ (m + 1) - 1) ≡ 0 [MOD 2 ^ (m + 1 + 1)]:= by
        suffices 2 ^ (m + 1 + 1) ∣ 2 ^ (2 * m + 2) * k ^ (k + 2 ^ (m + 1) - 1) by exact Nat.modEq_zero_iff_dvd.mpr this
        use 2 ^ m * k ^ (k + 2 ^ (m + 1) - 1)
        ring_nf
      replace h2:= Nat.ModEq.add_left (k ^ (k + 2 ^ (m + 1)) + 2 ^ (m + 1) * k ^ (k + 2 ^ (m + 1))) h2
      simp at h2
      replace h1:= Nat.ModEq.trans h1 h2
      -- Use Euler's theorem for powers of 2
      have g1 : Nat.Prime 2:= by norm_num
      replace g1:= Nat.totient_prime_pow g1 (show 0 < m + 1 + 1 by omega)
      simp at g1
      -- Show k is coprime with 2^(m+1+1)
      have g2 : Nat.Coprime 2 k:= by exact Nat.coprime_two_left.mpr hk
      replace g2 : Nat.Coprime (2 ^ (m + 1 + 1)) k:= by exact Nat.Coprime.pow_left (m + 1 + 1) g2
      replace g2 : Nat.Coprime k (2 ^ (m + 1 + 1)):= by exact Nat.coprime_comm.mp g2
      replace g2:= Nat.ModEq.pow_totient g2
      rw [g1] at g2
      replace g2:= Nat.ModEq.mul_right (k ^ k) g2
      rw [show k ^ 2 ^ (m + 1) * k ^ k = k ^ (2 ^ (m + 1) + k) by ring_nf] at g2
      simp at g2
      -- Show the remaining term is congruent to 2^(m+1)
      have g3 : 2 ^ (m + 1) * k ^ (k + 2 ^ (m + 1)) ≡ 2 ^ (m + 1) [MOD 2 ^ (m + 1 + 1)]:= by
        replace hk : Odd (k ^ (k + 2 ^ (m + 1))):= by exact Odd.pow hk
        rcases hk with ⟨a, ha⟩
        rw [ha]
        ring_nf
        -- Show the higher order term is divisible by 2^(m+1+1)
        have g3 : a * 2 ^ m * 4 ≡ 0 [MOD 2 ^ (m + 1 + 1)]:= by
          suffices 2 ^ (m + 1 + 1) ∣ a * 2 ^ m * 4 by exact Nat.modEq_zero_iff_dvd.mpr this
          use a
          ring_nf
        replace g3:= Nat.ModEq.add_right (2 ^ m * 2) g3
        simp at g3
        rw [show 2 ^ m * 4 = 2 ^ (m + 1 + 1) by ring]
        exact g3
      replace g2:= Nat.ModEq.add g2 g3
      rw [show 2 ^ (m + 1) + k = k + 2 ^ (m + 1) by ring] at g2
      exact Nat.ModEq.trans h1 g2
    -- Case analysis based on whether i and j are in the first or second half
    by_cases gi : i < 2 ^ m
    .
      -- Case 1: i < 2^m
      by_cases gj : j < 2 ^ m
      .
        -- Subcase 1.1: both i, j < 2^m - use induction hypothesis
        replace ih:= ih i gi j gj hij
        replace H:= Nat.ModEq.of_mul_right 2 H
        trivial
      .
        -- Subcase 1.2: i < 2^m, j ≥ 2^m
        simp at gj
        set j1:= j - 2 ^ m with hj1
        clear_value j1
        replace hj1 : j = j1 + 2 ^ m:= by omega
        subst j
        clear gj
        -- Apply the key lemma to j
        rw [show 2 * (j1 + 2 ^ m) + 1 = 2 * j1 + 1 + 2 ^ (m + 1) by omega] at H
        replace h1:= h1 (2 * j1 + 1) (by use j1)
        replace H:= Nat.ModEq.trans H h1
        rw [show f (2 * i + 1) = f (2 * i + 1) + 0 by simp] at H
        by_cases g : i = j1
        .
          -- If i = j1, we get a contradiction
          subst i
          replace H : 0 ≡ 2 ^ (m + 1) [MOD 2 ^ (m + 1 + 1)]:= by exact Nat.ModEq.add_left_cancel (id (Nat.ModEq.symm H)) rfl
          replace H : 2 ^ (m + 1 + 1) ∣ 2 ^ (m + 1):= by exact Nat.dvd_of_mod_eq_zero (id (Nat.ModEq.symm H))
          ring_nf at H
          replace H : 4 ∣ 2:= by
            have g1 : 2 ^ m > 0:= by positivity
            exact Nat.dvd_of_mul_dvd_mul_left g1 H
          omega
        .
          -- Otherwise, reduce modulo 2^(m+1) and use induction
          replace H:= Nat.ModEq.of_mul_right 2 H
          have g1 : 0 ≡ 2 ^ (m + 1) [MOD 2 ^ (m + 1)]:= by
            suffices 2 ^ (m + 1) ∣ 2 ^ (m + 1) by exact Dvd.dvd.zero_modEq_nat this
            simp
          replace H : f (2 * i + 1) ≡ f (2 * j1 + 1) [MOD 2 ^ (m + 1)]:= by exact Nat.ModEq.add_right_cancel g1 H
          ring_nf at hj
          replace ih:= ih i gi j1 (by omega) g
          trivial
    .
      -- Case 2: i ≥ 2^m
      set i1:= i - 2 ^ m with hi1
      clear_value i1
      replace hi1 : i = i1 + 2 ^ m:= by omega
      subst i
      clear gi
      ring_nf at hi
      by_cases gj : j < 2 ^ m
      .
        -- Subcase 2.1: i ≥ 2^m, j < 2^m
        rw [show 2 * (i1 + 2 ^ m) + 1 = 2 * i1 + 1 + 2 ^ (m + 1) by omega] at H
        replace h1:= h1 (2 * i1 + 1) (by use i1)
        replace H : f (2 * j + 1) ≡ f (2 * i1 + 1) + 2 ^ (m + 1) [MOD 2 ^ (m + 1 + 1)]:= by exact Nat.ModEq.trans (id (Nat.ModEq.symm H)) h1
        rw [show f (2 * j + 1) = f (2 * j + 1) + 0 by simp] at H
        by_cases g1 : j = i1
        .
          -- If j = i1, we get a contradiction
          subst j
          replace H : 0 ≡ 2 ^ (m + 1) [MOD 2 ^ (m + 1 + 1)]:= by exact Nat.ModEq.add_left_cancel (id (Nat.ModEq.symm H)) rfl
          replace H : 2 ^ (m + 1 + 1) ∣ 2 ^ (m + 1):= by exact Nat.dvd_of_mod_eq_zero (id (Nat.ModEq.symm H))
          ring_nf at H
          replace H : 4 ∣ 2:= by
            have g1 : 2 ^ m > 0:= by positivity
            exact Nat.dvd_of_mul_dvd_mul_left g1 H
          omega
        .
          -- Otherwise, reduce modulo 2^(m+1) and use induction
          replace H:= Nat.ModEq.of_mul_right 2 H
          have g1 : 0 ≡ 2 ^ (m + 1) [MOD 2 ^ (m + 1)]:= by
            suffices 2 ^ (m + 1) ∣ 2 ^ (m + 1) by exact Dvd.dvd.zero_modEq_nat this
            simp
          replace H : f (2 * j + 1) ≡ f (2 * i1 + 1) [MOD 2 ^ (m + 1)]:= by exact Nat.ModEq.add_right_cancel g1 H
          clear g1
          replace ih:= ih j gj i1 (by omega) g1
          trivial
      .
        -- Subcase 2.2: both i, j ≥ 2^m
        set j1:= j - 2 ^ m with hj1
        clear_value j1
        replace hj1 : j = j1 + 2 ^ m:= by omega
        subst j
        clear gj
        -- Apply the key lemma to both i and j
        rw [show 2 * (j1 + 2 ^ m) + 1 = 2 * j1 + 1 + 2 ^ (m + 1) by omega] at H
        rw [show 2 * (i1 + 2 ^ m) + 1 = 2 * i1 + 1 + 2 ^ (m + 1) by omega] at H
        have g1:= h1 (2 * i1 + 1) (by use i1)
        have g2:= h1 (2 * j1 + 1) (by use j1)
        replace g1:= Nat.ModEq.trans (id (Nat.ModEq.symm g1)) H
        replace g1:= Nat.ModEq.trans g1 g2
        -- Cancel the 2^(m+1) terms
        replace H : f (2 * i1 + 1) ≡ f (2 * j1 + 1) [MOD 2 ^ (m + 1 + 1)]:= by exact Nat.ModEq.add_right_cancel' (2 ^ (m + 1)) g1
        ring_nf at hj
        replace H:= Nat.ModEq.of_mul_right 2 H
        by_cases gij : i1 = j1
        .
          -- If i1 = j1, then i = j, contradiction
          absurd hij
          rw [gij]
        .
          -- Otherwise, use induction hypothesis
          replace ih:= ih i1 (by omega) j1 (by omega) gij
          simp at H
          trivial
