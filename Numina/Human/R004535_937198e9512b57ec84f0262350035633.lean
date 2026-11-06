import Mathlib
/- 19. (ROM 1) Consider the sequences $\left(a_{n}\right),\left(b_{n}\right)$ defined by
$$
a_{1}=3, \quad b_{1}=100, \quad a_{n+1}=3^{a_{n}}, \quad b_{n+1}=100^{b_{n}} .
$$

Find the smallest integer $m$ for which $b_{m}>a_{100}$. -/
theorem number_theory_280247 (a b : ℕ → ℕ) (ha1 : a 1 = 3) (hb1 : b 1 = 100) (ha : ∀ n : ℕ, a (n + 2) = 3 ^ a (n + 1)) (hb : ∀ n : ℕ, b (n + 2) = 100 ^ b (n + 1)) : IsLeast {m : ℕ | m > 0 ∧ b m > a 100} 99:= by
  constructor
  .
    -- First part: Show that b_99 > a_100 (i.e., 99 is in the set)
    simp
    -- Prove that for all n, b_{n+1} > a_{n+2}
    have h1 : ∀ n : ℕ, b (n + 1) > a (n + 2):= by
      intro n
      induction n with
      | zero =>
        -- Base case: b_1 > a_2, which is 100 > 3^3 = 27
        simp [hb1, ha 0, ha1]
      | succ n ih =>
        -- Inductive step: b_{n+2} > a_{n+3}
        rw [show n + 1 + 1 = n + 2 by omega]
        rw [ha (n + 1), hb n]
        rw [show n + 1 + 1 = n + 2 by omega]
        -- Show 100^{b_{n+1}} > 100^{a_{n+2}} using induction hypothesis
        have h1 : 100 ^ b (n + 1) > 100 ^ a (n + 2):= by
          have g : 100 > 1:= by omega
          exact (Nat.pow_lt_pow_iff_right g).mpr ih
        -- Show 100^{a_{n+2}} ≥ 3^{a_{n+2}} since 100 ≥ 3
        have h2 : 100 ^ a (n + 2) ≥ 3 ^ a (n + 2):= by
          have g : 100 ≥ 3:= by omega
          exact Nat.pow_le_pow_of_le_left g (a (n + 2))
        linarith
    -- Apply the lemma with n = 98 to get b_99 > a_100
    exact h1 98
  .
    -- Second part: Show that 99 is the least element (no smaller m works)
    simp [lowerBounds]
    intro n hn h
    -- Prove that b sequence is strictly increasing
    have h1 : ∀ n : ℕ, b (n + 2) > b (n + 1):= by
      intro n
      induction n with
      | zero =>
        -- Base case: b_2 > b_1, which is 100^100 > 100
        simp [hb 0, hb1]
      | succ n ih =>
        -- Inductive step: b_{n+3} > b_{n+2}
        rw [show n + 1 + 1 = n + 2 by omega]
        rw [hb n, hb (n + 1)]
        rw [show n + 1 + 1 = n + 2 by omega]
        have g : 100 > 1:= by omega
        exact (Nat.pow_lt_pow_iff_right g).mpr ih
    -- Assume for contradiction that there exists m < 99 with b_m > a_100
    by_contra H
    simp at H
    -- Prove a stronger monotonicity property
    replace h1 : ∀ m n : ℕ, b (m + 1) < b (n + m + 2):= by
      intro m n
      induction n with
      | zero =>
        -- Base case: b_{m+1} < b_{m+2}
        simp
        exact h1 m
      | succ n ih =>
        -- Inductive step: b_{m+1} < b_{n+m+3}
        replace h1:= h1 (n + m + 1)
        rw [show n + 1 + m + 2 = n + m + 3 by omega]
        rw [show n + m + 1 + 2 = n + m + 3 by omega] at h1
        rw [show n + m + 1 + 1 = n + m + 2 by omega] at h1
        linarith
    -- Show that if n < 99, then b_n ≤ b_98
    have h2 : b n ≤ b 98:= by
      by_cases h : n = 98
      .
        -- If n = 98, then b_n = b_98
        rw [h]
      .
        -- If n < 98, use monotonicity to show b_n < b_98
        replace h1:= h1 (n - 1) (97 - n)
        rw [show n - 1 + 1 = n by omega] at h1
        rw [show 97 - n + (n - 1) + 2 = 98 by omega] at h1
        linarith
    -- It suffices to show b_98 ≤ a_100 to get contradiction
    suffices b 98 ≤ a 100 by linarith
    clear h h2 H hn n
    -- Prove that a_{n+3} ≥ b_{n+1}^2 for all n
    have h2 : ∀ n : ℕ, a (n + 3) ≥ b (n + 1) ^ 2:= by
      intro n
      induction n with
      | zero =>
        -- Base case: a_3 ≥ b_1^2, which is 3^27 ≥ 100^2
        simp [ha 1, ha 0, ha1, hb1]
      | succ n ih =>
        -- Inductive step: a_{n+4} ≥ b_{n+2}^2
        rw [show n + 1 + 3 = n + 2 + 2 by omega]
        rw [show n + 1 + 1 = n + 2 by omega]
        rw [ha (n + 2), hb n]
        rw [show n + 2 + 1 = n + 3 by omega]
        -- Rewrite (100^{b_{n+1}})^2 = 100^{2*b_{n+1}}
        rw [show (100 ^ b (n + 1)) ^ 2 = 100 ^ (2 * b (n + 1)) by ring]
        -- Use induction hypothesis: 3^{a_{n+3}} ≥ 3^{b_{n+1}^2}
        replace ih : 3 ^ a (n + 3) ≥ 3 ^ (b (n + 1) ^ 2):= by refine Nat.pow_le_pow_of_le_right (by omega) ih
        -- Show b_{n+1}^2 ≥ 10*b_{n+1} for large enough n
        have h2 : b (n + 1) ^ 2 ≥ 10 * b (n + 1):= by
          rw [show b (n + 1) ^ 2 = b (n + 1) * b (n + 1) by ring]
          suffices b (n + 1) ≥ 10 by exact Nat.mul_le_mul_right (b (n + 1)) this
          by_cases hn : n = 0
          .
            -- If n = 0, b_1 = 100 ≥ 10
            subst n
            simp [hb1]
          .
            -- If n > 0, use monotonicity to show b_{n+1} ≥ 100 ≥ 10
            replace h1:= h1 0 (n - 1)
            rw [show n - 1 + 0 + 2 = n + 1 by omega] at h1
            simp [hb1] at h1
            linarith
        -- Use the inequality: 3^{b_{n+1}^2} ≥ 3^{10*b_{n+1}}
        replace h2 : 3 ^ (b (n + 1) ^ 2) ≥ 3 ^ (10 * b (n + 1)):= by exact Nat.pow_le_pow_of_le_right (by omega) h2
        -- Rewrite 3^{10*b_{n+1}} = 3^{5*(2*b_{n+1})} = (3^5)^{2*b_{n+1}}
        rw [show 10 * b (n + 1) = 5 * (2 * b (n + 1)) by omega] at h2
        rw [show 3 ^ (5 * (2 * b (n + 1))) = (3 ^ 5) ^ (2 * b (n + 1)) by exact Nat.pow_mul 3 5 (2 * b (n + 1))] at h2
        simp at h2
        -- Show 243 ≥ 100, so 243^{2*b_{n+1}} ≥ 100^{2*b_{n+1}}
        have h3 : 243 ≥ 100:= by omega
        replace h3 : 243 ^ (2 * b (n + 1)) ≥ 100 ^ (2 * b (n + 1)):= by exact Nat.pow_le_pow_of_le_left h3 (2 * b (n + 1))
        linarith
    -- Apply the lemma with n = 97 to get a_100 ≥ b_98^2
    replace h2:= h2 97
    simp at h2
    -- Show b_98 ≥ 1
    replace h1:= h1 0 96
    simp [hb1] at h1
    replace h1 : b 98 ≥ 1:= by omega
    -- Show b_98^2 ≥ b_98 since b_98 ≥ 1
    replace h1 : b 98 * b 98 ≥ b 98:= by exact Nat.le_mul_of_pos_left (b 98) h1
    -- Final contradiction: a_100 ≥ b_98^2 ≥ b_98, but we need b_98 > a_100
    linarith
