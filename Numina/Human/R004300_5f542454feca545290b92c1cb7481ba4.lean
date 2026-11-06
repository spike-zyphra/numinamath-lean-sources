import Mathlib
/- ## Task 1.

Determine all sequences $a: \mathbb{N} \rightarrow \mathbb{N}$ such that for all $n \in \mathbb{N}$, the following holds:

$$
a_{n}+a_{n+1}=a_{n+2} a_{n+3}-200
$$ -/
theorem algebra_250100 : {a : ℕ → ℕ | ∀ n : ℕ, a n + a (n + 1) + 200 = a (n + 2) * a (n + 3)} = {a : ℕ → ℕ | (∃ b c : ℕ, (b, c) ∈ ({(2, 202), (202, 2), (4, 68), (68, 4)} : Set (ℕ × ℕ)) ∧ (∀ n : ℕ, a (2 * n) = b ∧ a (2 * n + 1) = c)) ∨ (∃ b : ℕ, ∀ n : ℕ, (a (2 * n) = 1 ∧ a (2 * n + 1) = b + 201 * n)) ∨ (∃ c : ℕ, ∀ n : ℕ, (a (2 * n + 1) = 1 ∧ a (2 * n) = c + 201 * n))}:= by
  ext a
  constructor
  .
    -- Forward direction: If a satisfies the recurrence relation, then it has one of the three forms
    intro h
    simp at h
    -- Key identity: a_n - a_{n+2} = a_{n+3} * (a_{n+2} - a_{n+4})
    have h1 : ∀ n : ℕ, (a n : ℤ) - a (n + 2) = a (n + 3) * (a (n + 2) - a (n + 4)):= by
      intro n
      have g1:= h n
      have g2:= h (n + 1)
      ring_nf at g1 g2 ⊢
      zify at g1 g2
      linarith
    -- Prove that a_n ≤ a_{n+2} for all n (monotonicity)
    have h2 : ∀ n : ℕ, a n ≤ a (n + 2):= by
      intro n
      by_contra H
      simp at H
      -- If a_n > a_{n+2}, then a_{n+2k} + k ≤ a_n for all k
      have h2 : ∀ k : ℕ, a (n + 2 * k) + k ≤ a n:= by
        intro k
        induction k with
        | zero =>
          simp
        | succ k ih =>
          suffices a (n + 2 * (k + 1)) < a (n + 2 * k) by linarith
          replace H : ∀ k : ℕ, a (n + 2 * (k + 1)) < a (n + 2 * k):= by
            intro k
            induction k with
            | zero =>
              simp
              exact H
            | succ k ih =>
              rw [show n + 2 * (k + 1 + 1) = n + 2 * k + 4 by omega]
              rw [show n + 2 * (k + 1) = n + 2 * k + 2 by omega] at ih ⊢
              zify at ih ⊢
              replace h1:= h1 (n + 2 * k)
              replace ih : (a (n + 2 * k) : ℤ) - (a (n + 2 * k + 2)) > 0:= by linarith
              rw [h1] at ih
              have h2 : a (n + 2 * k + 3) > 0:= by
                replace h:= h (n + 2 * k)
                by_contra H
                simp at H
                rw [H] at h
                simp at h
              zify at h2
              suffices (a (n + 2 * k + 2) : ℤ) - (a (n + 2 * k + 4)) > 0 by linarith
              exact (pos_iff_pos_of_mul_pos ih).mp h2
          exact H k
      replace h2:= h2 (a n + 1)
      omega
    -- Case analysis: a_0 = a_2 or a_0 ≠ a_2
    by_cases g : a 0 = a 2
    .
      -- Case 1: a_0 = a_2, which implies a_{2n} = a_0 for all n
      replace g : ∀ n : ℕ, a (2 * n) = a 0:= by
        intro n
        induction n with
        | zero =>
          simp
        | succ n ih =>
          replace g : ∀ n : ℕ, a (2 * n) = a (2 * n + 2):= by
            intro n
            induction n with
            | zero =>
              simp
              exact g
            | succ n ih =>
              replace h1:= h1 (2 * n)
              rw [ih] at h1
              have g1 : a (2 * n + 3) ≠ 0:= by
                by_contra H
                replace h:= h (2 * n)
                rw [H] at h
                simp at h
              simp [g1] at h1
              ring_nf at h1 ⊢
              zify
              linarith
          replace g:= g n
          rw [show 2 * (n + 1) = 2 * n + 2 by omega]
          linarith
      -- Key identity for odd indices: (a_{2n+1} - a_{2n+3}) * a_0^n = a_1 - a_3
      replace h1 : ∀ n : ℕ, ((a (2 * n + 1) : ℤ) - (a (2 * n + 3))) * (a 0) ^ n = (a 1 - a 3):= by
        intro n
        induction n with
        | zero =>
          simp
        | succ n ih =>
          rw [show 2 * (n + 1) + 1 = 2 * n + 3 by omega]
          rw [show 2 * (n + 1) + 3 = 2 * n + 5 by omega]
          replace h1:= h1 (2 * n + 1)
          rw [show 2 * n + 1 + 2 = 2 * n + 3 by omega] at h1
          rw [show 2 * n + 1 + 3 = 2 * (n + 2) by omega] at h1
          rw [show 2 * n + 1 + 4 = 2 * n + 5 by omega] at h1
          rw [←ih]
          rw [g (n + 2)] at h1
          rw [h1]
          ring_nf
      -- Subcase: a_1 = a_3 or a_1 ≠ a_3
      by_cases g1 : a 1 = a 3
      .
        -- Subcase 1: a_1 = a_3, which implies a_{2n+1} = a_1 for all n
        replace g1 : ∀ n : ℕ, a (2 * n + 1) = a 1:= by
          intro n
          induction n with
          | zero =>
            simp
          | succ n ih =>
            rw [show 2 * (n + 1) + 1 = 2 * n + 3 by omega]
            replace h1:= h1 n
            rw [g1] at h1
            simp at h1
            rcases h1 with h1 | h1
            .
              zify at ih ⊢
              linarith
            .
              replace h1:= h1.1
              replace h:= h 1
              replace g:= g 2
              simp at g
              ring_nf at h
              rw [g, h1] at h
              simp at h
        -- Now we have a_{2n} = a_0 and a_{2n+1} = a_1 for all n
        replace h:= h 0
        ring_nf at h
        have g2:= g1 1
        ring_nf at g2
        rw [g2] at h
        have g3:= g 1
        ring_nf at g3
        rw [g3] at h
        -- Prove that (a_0, a_1) must be one of the four pairs
        replace h : (a 0, a 1) ∈ ({(2, 202), (202, 2), (4, 68), (68, 4)} : Set (ℕ × ℕ)):= by
          replace g2 : a 0 ≠ 0:= by
            by_contra H
            rw [H] at h
            simp at h
          replace g3 : a 1 ≠ 0:= by
            by_contra H
            rw [H] at h
            simp at h
          set b:= a 0 - 1 with hb
          set c:= a 1 - 1 with hc
          clear_value b c
          replace hb : a 0 = b + 1:= by omega
          replace hc : a 1 = c + 1:= by omega
          rw [hb, hc] at h ⊢
          replace h : b * c = 201:= by linarith
          have g4 : b ∈ Nat.divisors 201:= by
            replace h : b ∣ 201:= by
              use c
              linarith
            refine Nat.mem_divisors.mpr ⟨h, (by omega)⟩
          have g5 : Nat.divisors 201 = {1, 3, 67, 201}:= by native_decide
          rw [g5] at g4
          fin_cases g4
          .
            simp at h
            subst c
            simp
          .
            replace h : c = 67:= by omega
            subst c
            simp
          .
            replace h : c = 3:= by omega
            subst c
            simp
          .
            replace h : c = 1:= by omega
            subst c
            simp
        simp at h ⊢
        left
        use a 0, a 1
        simp [h]
        intro n
        exact ⟨g n, g1 n⟩
      .
        -- Subcase 2: a_1 ≠ a_3, which forces a_0 = 1
        have g2 : a 0 ≠ 0:= by
          by_contra H
          replace g:= g 2
          ring_nf at g
          replace h:= h 1
          ring_nf at h
          rw [g, H] at h
          simp at h
        replace g2 : a 0 = 1:= by
          by_contra H
          replace H : a 0 ≥ 2:= by omega
          -- If a_0 ≥ 2, then |a_1 - a_3| grows exponentially
          replace h1 : ∀ n : ℕ, |(a 1 : ℤ) - a 3| ≥ 2 ^ n:= by
            intro n
            replace h1:= h1 n
            rw [←h1]
            rw [abs_mul _ _]
            have g3 : (a (2 * n + 1) : ℤ) - a (2 * n + 3) ≠ 0:= by
              by_contra H
              rw [H] at h1
              simp at h1
              absurd g1
              zify
              linarith
            replace g3 : |(a (2 * n + 1) : ℤ) - a (2 * n + 3)| > 0:= by positivity
            replace g3 : |(a (2 * n + 1) : ℤ) - a (2 * n + 3)| ≥ 1:= by omega
            have g4 : (a 0) ^ n > 0:= by positivity
            zify at g4
            rw [abs_of_pos g4]
            replace H : (a 0) ^ n ≥ 2 ^ n:= by exact Nat.pow_le_pow_of_le_left H n
            zify at H
            rw [show (2 : ℤ) ^ n = 1 * 2 ^ n by simp]
            have g5 : (2 : ℤ) ^ n ≥ 0:= by positivity
            refine Int.mul_le_mul g3 H g5 (by positivity)
          have h2 : ∀ n : ℕ, 2 ^ n ≥ n + 1:= by
            intro n
            induction n with
            | zero =>
              simp
            | succ n ih =>
              ring_nf
              linarith
          set t:= |↑(a 1 : ℤ) - ↑(a 3 : ℤ)| with ht
          clear_value t
          replace ht : t ≥ 0:= by subst t ; positivity
          replace h1:= h1 (t.natAbs)
          replace h2:= h2 (t.natAbs)
          zify at h2
          rw [abs_of_nonneg ht] at h2
          linarith
        rw [g2] at g h1
        simp at h1
        replace h:= h 0
        ring_nf at h
        have g3:= g 1
        ring_nf at g3
        rw [g2, g3] at h
        simp at h
        -- Now a_{2n+3} = a_{2n+1} + 201 for all n
        replace h1 : ∀ n : ℕ, a (2 * n + 3) = a (2 * n + 1) + 201:= by
          intro n
          zify
          replace h1:= h1 n
          linarith
        -- This gives a_{2n+1} = a_1 + 201 * n for all n
        replace h1 : ∀ n : ℕ, a (2 * n + 1) = a 1 + 201 * n:= by
          intro n
          induction n with
          | zero =>
            simp
          | succ n ih =>
            rw [show 2 * (n + 1) + 1 = 2 * n + 3 by omega]
            replace h1:= h1 n
            linarith
        simp
        right
        left
        use a 1
        intro n
        exact ⟨g n, h1 n⟩
    .
      -- Case 2: a_0 ≠ a_2, which forces a_1 = a_3
      by_cases g1 : a 1 ≠ a 3
      .
        -- Subcase: a_1 ≠ a_3, which leads to a contradiction
        replace g : ∀ n : ℕ, a (2 * n + 2) > a (2 * n):= by
          intro n
          induction n with
          | zero =>
            simp
            replace h2:= h2 0
            simp at h2
            omega
          | succ n ih =>
            rw [show 2 * (n + 1) + 2 = 2 * n + 4 by omega]
            rw [show 2 * (n + 1) = 2 * n + 2 by omega]
            replace h1:= h1 (2 * n)
            have g2 : a (2 * n + 3) > 0:= by
              by_contra H
              simp at H
              replace h:= h (2 * n)
              rw [H] at h
              simp at h
            zify at ih g2
            replace ih : (a (2 * n) : ℤ) - (a (2 * n + 2)) < 0:= by linarith
            zify
            suffices  (a (2 * n + 2) : ℤ) - (a (2 * n + 4)) < 0 by linarith
            rw [h1] at ih
            exact (pos_iff_neg_of_mul_neg ih).mp g2
        replace g1 : ∀ n : ℕ, a (2 * n + 3) > a (2 * n + 1):= by
          intro n
          induction n with
          | zero =>
            simp
            replace h2:= h2 1
            simp at h2
            omega
          | succ n ih =>
            rw [show 2 * (n + 1) + 3 = 2 * n + 5 by omega]
            rw [show 2 * (n + 1) + 1 = 2 * n + 3 by omega]
            replace h1:= h1 (2 * n + 1)
            have g2 : a (2 * n + 4) > 0:= by
              by_contra H
              simp at H
              replace h:= h (2 * n + 1)
              rw [H] at h
              simp at h
            zify at ih g2 ⊢
            replace ih : (a (2 * n + 1) : ℤ) - (a (2 * n + 3)) < 0:= by linarith
            suffices (a (2 * n + 3) : ℤ) - (a (2 * n + 5)) < 0 by linarith
            rw [h1] at ih
            exact (pos_iff_neg_of_mul_neg ih).mp g2
        replace g : ∀ n : ℕ, a (2 * n) ≥ n:= by
          intro n
          induction n with
          | zero =>
            simp
          | succ n ih =>
            rw [show 2 * (n + 1) = 2 * n + 2 by omega]
            replace g:= g n
            linarith
        replace g1 : ∀ n : ℕ, a (2 * n + 1) ≥ n:= by
          intro n
          induction n with
          | zero =>
            simp
          | succ n ih =>
            rw [show 2 * (n + 1) + 1 = 2 * n + 3 by omega]
            replace g1:= g1 n
            linarith
        replace g:= g 16
        replace g1:= g1 16
        ring_nf at g g1
        replace h:= h 30
        ring_nf at h
        have g2:= h2 30
        have g3:= h2 31
        ring_nf at g2 g3
        set x:= a 32 - 1 with hx
        set y:= a 33 - 1 with hy
        clear_value x y
        replace hx : a 32 = x + 1:= by omega
        replace hy : a 33 = y + 1:= by omega
        rw [hx] at g2 h
        rw [hy] at g3 h
        replace g : x ≥ 15:= by omega
        replace g1 : y ≥ 15:= by omega
        replace g : x * y ≥ 15 * 15:= by exact Nat.mul_le_mul g g1
        linarith
      .
        -- Subcase: a_1 = a_3, which implies a_{2n+1} = a_1 for all n
        simp at g1
        replace g1 : ∀ n : ℕ, a (2 * n + 1) = a 1:= by
          intro n
          induction n with
          | zero =>
            simp
          | succ n ih =>
            rw [show 2 * (n + 1) + 1 = 2 * n + 3 by omega]
            replace g1 : ∀ n : ℕ, a (2 * n + 1) = a (2 * n + 3):= by
              intro n
              induction n with
              | zero =>
                simp
                exact g1
              | succ n ih =>
                rw [show 2 * (n + 1) + 3 = 2 * n + 5 by omega]
                rw [show 2 * (n + 1) + 1 = 2 * n + 3 by omega]
                replace h1:= h1 (2 * n + 1)
                rw [show 2 * n + 1 + 2 = 2 * n + 3 by omega] at h1
                rw [show 2 * n + 1 + 3 = 2 * n + 4 by omega] at h1
                rw [show 2 * n + 1 + 4 = 2 * n + 5 by omega] at h1
                have g2 : a (2 * n + 4) ≠ 0:= by
                  by_contra H
                  replace h:= h (2 * n + 1)
                  ring_nf at h H
                  rw [H] at h
                  simp at h
                rw [ih] at h1
                simp [g2] at h1
                zify
                linarith
            replace g1:= g1 n
            linarith
        -- Key identity for even indices: (a_{2n} - a_{2n+2}) * a_1^n = a_0 - a_2
        replace h1 : ∀ n : ℕ, ((a (2 * n) : ℤ) - (a (2 * n + 2))) * (a 1) ^ n = (a 0 - a 2):= by
          intro n
          induction n with
          | zero =>
            simp
          | succ n ih =>
            rw [show 2 * (n + 1) = 2 * n + 2 by omega]
            rw [show 2 * n + 2 + 2 = 2 * n + 4 by omega]
            replace h1:= h1 (2 * n)
            replace g1:= g1 (n + 1)
            rw [show 2 * (n + 1) + 1 = 2 * n + 3 by omega] at g1
            rw [g1] at h1
            rw [←ih, h1]
            ring_nf
        have g2 : a 1 ≠ 0:= by
          by_contra H
          replace g1:= g1 1
          ring_nf at g1
          replace h:= h 0
          ring_nf at h
          rw [g1, H] at h
          simp at h
        replace g2 : a 1 = 1:= by
          by_contra H
          replace H : a 1 ≥ 2:= by omega
          -- If a_1 ≥ 2, then |a_0 - a_2| grows exponentially
          replace h1 : ∀ n : ℕ, |(a 0 : ℤ) - a 2| ≥ 2 ^ n:= by
            intro n
            replace h1:= h1 n
            rw [←h1]
            rw [abs_mul _ _]
            have g3 : (a (2 * n) : ℤ) - a (2 * n + 2) ≠ 0:= by
              by_contra H
              rw [H] at h1
              simp at h1
              absurd g
              zify
              linarith
            replace g3 : |(a (2 * n) : ℤ) - a (2 * n + 2)| > 0:= by positivity
            replace g3 : |(a (2 * n) : ℤ) - a (2 * n + 2)| ≥ 1:= by omega
            have g4 : (a 1) ^ n > 0:= by positivity
            zify at g4
            rw [abs_of_pos g4]
            replace H : (a 1) ^ n ≥ 2 ^ n:= by exact Nat.pow_le_pow_of_le_left H n
            zify at H
            rw [show (2 : ℤ) ^ n = 1 * 2 ^ n by simp]
            have g5 : (2 : ℤ) ^ n ≥ 0:= by positivity
            refine Int.mul_le_mul g3 H g5 (by positivity)
          have h3 : ∀ n : ℕ, 2 ^ n ≥ n + 1:= by
            intro n
            induction n with
            | zero =>
              simp
            | succ n ih =>
              ring_nf
              linarith
          set t:= |↑(a 0 : ℤ) - ↑(a 2 : ℤ)| with ht
          clear_value t
          replace ht : t ≥ 0:= by subst t ; positivity
          replace h1:= h1 (t.natAbs)
          replace h3:= h3 (t.natAbs)
          zify at h3
          rw [abs_of_nonneg ht] at h3
          linarith
        rw [g2] at h1 g1
        simp at h1
        -- Now a_{2n+2} = a_{2n} + 201 for all n
        replace h : ∀ n : ℕ, a (2 * n + 2) = a (2 * n) + 201:= by
          intro n
          replace h:= h (2 * n)
          rw [g1 n] at h
          replace g1:= g1 (n + 1)
          rw [show 2 * (n + 1) + 1 = 2 * n + 3 by omega] at g1
          rw [g1] at h
          linarith
        -- This gives a_{2n} = a_0 + 201 * n for all n
        replace h : ∀ n : ℕ, a (2 * n) = a 0 + 201 * n:= by
          intro n
          induction n with
          | zero =>
            simp
          | succ n ih =>
            rw [show 2 * (n + 1) = 2 * n + 2 by omega]
            replace h:= h n
            linarith
        simp
        right
        right
        use a 0
        intro n
        exact ⟨g1 n, h n⟩
  .
    -- Backward direction: If a has one of the three forms, then it satisfies the recurrence relation
    intro h
    simp at h
    rcases h with h | h | h
    .
      -- Case 1: Constant sequences with (a_0, a_1) in the four specific pairs
      rcases h with ⟨b, c, h, h1⟩
      rcases h with h | h | h | h
      all_goals
        rcases h with ⟨rfl, rfl⟩
        simp
        intro n
        by_cases g : Odd n
        .
          rcases g with ⟨n, rfl⟩
          have g1:= h1 n
          have g2:= h1 (n + 1)
          have g3:= h1 (n + 2)
          ring_nf at g1 g2 g3 ⊢
          rw [g1.2, g2.1, g2.2, g3.1]
          simp
        .
          simp at g
          rcases g with ⟨n, rfl⟩
          have g1:= h1 n
          have g2:= h1 (n + 1)
          ring_nf at g1 g2 ⊢
          rw [g1.1, g1.2, g2.1, g2.2]
          simp
    .
      -- Case 2: Sequences with a_{2n} = 1 and a_{2n+1} = b + 201 * n
      rcases h with ⟨b, h1⟩
      simp
      intro n
      by_cases g : Odd n
      .
        rcases g with ⟨n, rfl⟩
        have g1:= h1 n
        have g2:= h1 (n + 1)
        have g3:= h1 (n + 2)
        ring_nf at g1 g2 g3 ⊢
        rw [g1.2, g2.1, g2.2, g3.1]
        ring_nf
      .
        simp at g
        rcases g with ⟨n, rfl⟩
        have g1:= h1 n
        have g2:= h1 (n + 1)
        ring_nf at g1 g2 ⊢
        rw [g1.1, g1.2, g2.1, g2.2]
        ring_nf
    .
      -- Case 3: Sequences with a_{2n+1} = 1 and a_{2n} = c + 201 * n
      rcases h with ⟨b, h1⟩
      simp
      intro n
      by_cases g : Odd n
      .
        rcases g with ⟨n, rfl⟩
        have g1:= h1 n
        have g2:= h1 (n + 1)
        have g3:= h1 (n + 2)
        ring_nf at g1 g2 g3 ⊢
        rw [g1.1, g2.2, g2.1, g3.2]
        ring_nf
      .
        simp at g
        rcases g with ⟨n, rfl⟩
        have g1:= h1 n
        have g2:= h1 (n + 1)
        ring_nf at g1 g2 ⊢
        rw [g1.1, g1.2, g2.1, g2.2]
        ring_nf
