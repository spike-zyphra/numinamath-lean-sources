import Mathlib
/- Let $n$ be a positive integer not divisible by 2 or 3 . Prove that for all integers $k$, the number $(k+1)^{n}-k^{n}-1$ is divisible by $k^{2}+k+1$. -/
theorem number_theory_604640 (n : ℕ) (hn : n > 0) (h2 : ¬2 ∣ n) (h3 : ¬3 ∣ n) : ∀ k : ℤ, (k ^ 2 + k + 1) ∣ (k + 1) ^ n - k ^ n - 1:= by
    -- First, we prove that n must be congruent to either 1 or 5 modulo 6
    have h1 : n ≡ 1 [MOD 6] ∨ n ≡ 5 [MOD 6]:= by
        -- Establish that 2 and 3 divide 6
        have g1 : 2 ∣ 6:= by omega
        have g2 : 3 ∣ 6:= by omega
        -- Check all possible cases for n modulo 6
        mod_cases n % 6
        .
            -- Case n ≡ 0 [MOD 6]: This contradicts our assumption that n is not divisible by 2
            replace H : n ≡ 0 [MOD 2]:= by exact Nat.ModEq.symm (Nat.ModEq.of_dvd g1 (id (Nat.ModEq.symm H)))
            replace H : 2 ∣ n:= by exact Nat.dvd_of_mod_eq_zero H
            trivial
        .
            -- Case n ≡ 1 [MOD 6]: This is valid
            left
            exact H
        .
            -- Case n ≡ 2 [MOD 6]: This contradicts our assumption that n is not divisible by 2
            replace H : n ≡ 2 [MOD 2]:= by exact Nat.ModEq.symm (Nat.ModEq.of_dvd g1 (id (Nat.ModEq.symm H)))
            replace H : 2 ∣ n:= by exact Nat.dvd_of_mod_eq_zero H
            trivial
        .
            -- Case n ≡ 3 [MOD 6]: This contradicts our assumption that n is not divisible by 3
            replace H : n ≡ 3 [MOD 3]:= by exact Nat.ModEq.symm (Nat.ModEq.of_dvd g2 (id (Nat.ModEq.symm H)))
            replace H : 3 ∣ n:= by exact Nat.dvd_of_mod_eq_zero H
            trivial
        .
            -- Case n ≡ 4 [MOD 6]: This contradicts our assumption that n is not divisible by 2
            replace H : n ≡ 4 [MOD 2]:= by exact Nat.ModEq.symm (Nat.ModEq.of_dvd g1 (id (Nat.ModEq.symm H)))
            replace H : 2 ∣ n:= by exact Nat.dvd_of_mod_eq_zero H
            trivial
        .
            -- Case n ≡ 5 [MOD 6]: This is valid
            right
            exact H

    -- Handle the special case where n = 1
    by_cases h4 : n = 1
    .
        -- For n = 1, the statement is trivial
        subst n
        simp
    .
        -- For n ≠ 1, we can prove that n ≥ 5
        replace h4 : n ≥ 5:= by
            by_contra H
            simp at H
            replace H : n = 2 ∨ n = 3 ∨ n = 4:= by omega
            rcases H with H | H | H
            all_goals
                subst n
                omega

        -- We no longer need the assumptions that n is not divisible by 2 or 3
        clear h2 h3
        intro k

        -- We prove that for t = 1 or t = 5, and for any m, the property holds for n = 6m + t
        have h2 : ∀ t : ℕ, t = 1 ∨ t = 5 → (∀ m : ℕ, k ^ 2 + k + 1 ∣ (k + 1) ^ (6 * m + t) - k ^ (6 * m + t) - 1):= by
            intro t ht m
            induction m with
            | zero =>
                -- Base cases: m = 0, so we check t = 1 and t = 5
                simp
                rcases ht with ht | ht
                .
                    -- Case t = 1: Direct verification
                    subst t
                    simp
                .
                    -- Case t = 5: Algebraic manipulation to show divisibility
                    subst t
                    ring_nf
                    rw [show k * 5 + k ^ 2 * 10 + k ^ 3 * 10 + k ^ 4 * 5 = 5 * k * (k + 1) * (1 + k + k ^ 2) by ring]
                    simp
            | succ m ih =>
                -- Inductive step: Assume the property holds for m, prove for m+1
                set T:= k ^ 2 + k + 1 with hT
                clear_value T

                -- We'll prove this using modular arithmetic
                suffices (k + 1) ^ (6 * (m + 1) + t) - k ^ (6 * (m + 1) + t) - 1 ≡ 0 [ZMOD T] by exact Int.dvd_of_emod_eq_zero this

                -- By induction hypothesis, the property holds for 6m + t
                replace ih : (k + 1) ^ (6 * m + t) - k ^ (6 * m + t) - 1 ≡ 0 [ZMOD T]:= by exact Dvd.dvd.modEq_zero_int ih

                -- Key lemma 1: For any n, (k+1)^(n+3) + k^(n+3) ≡ -((k+1)^n - k^n) [MOD T]
                have h3 : ∀ n : ℕ, (k + 1) ^ (n + 3) + k ^ (n + 3) ≡ - ((k + 1) ^ n - k ^ n) [ZMOD T]:= by
                    intro n
                    rw [show n + 3 = 2 + (n + 1) by ring]
                    rw [show (k + 1) ^ (2 + (n + 1)) + k ^ (2 + (n + 1)) = (k + 1) ^ 2 * (k + 1) ^ (n + 1) + k ^ 2 * k ^ (n + 1) by ring]
                    rw [show (k + 1) ^ 2 = k + T by linarith]
                    rw [show k ^ 2 = T - (k + 1) by linarith]
                    have g1 : T ≡ 0 [ZMOD T]:= by refine Dvd.dvd.modEq_zero_int (by simp)
                    have g2 : T - (k + 1) ≡ 0 -(k + 1) [ZMOD T]:= by exact Int.ModEq.sub g1 rfl
                    replace g1 : k + T ≡ k [ZMOD T]:= by simp
                    simp at g2
                    rw [show -1 + -k = -(k + 1) by ring] at g2
                    replace g1 : (k + T) * (k + 1) ^ (n + 1) ≡ k * (k + 1) ^ (n + 1) [ZMOD T]:= by exact Int.ModEq.mul g1 rfl
                    replace g2 : (T - (k + 1)) * k ^ (n + 1) ≡ -(k + 1) * k ^ (n + 1) [ZMOD T]:= by exact Int.ModEq.mul g2 rfl
                    have g3 : (k + T) * (k + 1) ^ (n + 1) + (T - (k + 1)) * k ^ (n + 1) ≡ k * (k + 1) ^ (n + 1) + -(k + 1) * k ^ (n + 1) [ZMOD T]:= by exact Int.ModEq.add g1 g2
                    clear g1 g2
                    suffices k * (k + 1) ^ (n + 1) + -(k + 1) * k ^ (n + 1) ≡ -((k + 1) ^ n - k ^ n) [ZMOD T] by exact Int.ModEq.symm (Int.ModEq.trans (id (Int.ModEq.symm this)) (id (Int.ModEq.symm g3)))
                    clear g3
                    rw [show n + 1 = 1 + n by ring]
                    rw [show (k + 1) ^ (1 + n) = (k + 1) * (k + 1) ^ n by ring]
                    rw [show k ^ (1 + n) = k * k ^ n by ring]
                    simp
                    rw [show k * ((k + 1) * (k + 1) ^ n) + (-1 + -k) * (k * k ^ n) = k * (k + 1) * ((k + 1) ^ n - k ^ n) by ring]
                    rw [show k * (k + 1) = T - 1 by linarith]
                    have g1 : T ≡ 0 [ZMOD T]:= by refine Dvd.dvd.modEq_zero_int (by simp)
                    replace g1 : T - 1 ≡ 0 - 1 [ZMOD T]:= by exact Int.ModEq.sub g1 rfl
                    simp at g1
                    replace g1 : (T - 1) * ((k + 1) ^ n - k ^ n) ≡ (-1) * ((k + 1) ^ n - k ^ n) [ZMOD T]:= by exact Int.ModEq.mul g1 rfl
                    rw [show (-1) * ((k + 1) ^ n - k ^ n) = k ^ n - (k + 1) ^ n by ring] at g1
                    exact g1

                -- Key lemma 2: For any n, (k+1)^(n+3) - k^(n+3) ≡ -((k+1)^n + k^n) [MOD T]
                have h2 : ∀ n : ℕ, (k + 1) ^ (n + 3) - k ^ (n + 3) ≡ -((k + 1) ^ n + k ^ n) [ZMOD T]:= by
                    intro n
                    rw [show n + 3 = 2 + (n + 1) by ring]
                    rw [show (k + 1) ^ (2 + (n + 1)) - k ^ (2 + (n + 1)) = (k + 1) ^ 2 * (k + 1) ^ (n + 1) - k ^ 2 * k ^ (n + 1) by ring]
                    rw [show (k + 1) ^ 2 = k + T by linarith]
                    rw [show k ^ 2 = T - (k + 1) by linarith]
                    have g1 : T ≡ 0 [ZMOD T]:= by refine Dvd.dvd.modEq_zero_int (by simp)
                    have g2 : T - (k + 1) ≡ 0 -(k + 1) [ZMOD T]:= by exact Int.ModEq.sub g1 rfl
                    replace g1 : k + T ≡ k [ZMOD T]:= by simp
                    simp at g2
                    rw [show -1 + -k = -(k + 1) by ring] at g2
                    replace g1 : (k + T) * (k + 1) ^ (n + 1) ≡ k * (k + 1) ^ (n + 1) [ZMOD T]:= by exact Int.ModEq.mul g1 rfl
                    replace g2 : (T - (k + 1)) * k ^ (n + 1) ≡ -(k + 1) * k ^ (n + 1) [ZMOD T]:= by exact Int.ModEq.mul g2 rfl
                    have g3 : (k + T) * (k + 1) ^ (n + 1) - (T - (k + 1)) * k ^ (n + 1) ≡ k * (k + 1) ^ (n + 1) - -(k + 1) * k ^ (n + 1) [ZMOD T]:= by exact Int.ModEq.sub g1 g2
                    clear g1 g2
                    suffices k * (k + 1) ^ (n + 1) - -(k + 1) * k ^ (n + 1) ≡ -((k + 1) ^ n + k ^ n) [ZMOD T] by exact Int.ModEq.symm (Int.ModEq.trans (id (Int.ModEq.symm this)) (id (Int.ModEq.symm g3)))
                    clear g3
                    rw [show n + 1 = 1 + n by ring]
                    rw [show (k + 1) ^ (1 + n) = (k + 1) * (k + 1) ^ n by ring]
                    rw [show k ^ (1 + n) = k * k ^ n by ring]
                    simp
                    rw [show k * ((k + 1) * (k + 1) ^ n) - (-1 + -k) * (k * k ^ n) = k * (k + 1) * ((k + 1) ^ n + k ^ n) by ring]
                    rw [show k * (k + 1) = T - 1 by linarith]
                    have g1 : T ≡ 0 [ZMOD T]:= by refine Dvd.dvd.modEq_zero_int (by simp)
                    replace g1 : T - 1 ≡ 0 - 1 [ZMOD T]:= by exact Int.ModEq.sub g1 rfl
                    simp at g1
                    replace g1 : (T - 1) * ((k + 1) ^ n + k ^ n) ≡ (-1) * ((k + 1) ^ n + k ^ n) [ZMOD T]:= by exact Int.ModEq.mul g1 rfl
                    rw [show (-1) * ((k + 1) ^ n + k ^ n) = -k ^ n + -(k + 1) ^ n by ring] at g1
                    exact g1

                -- Apply the lemmas to complete the induction
                specialize h2 (6 * m + t + 3)
                specialize h3 (6 * m + t)
                rw [show 6 * m + t + 3 + 3 = 6 * (m + 1) + t by ring] at h2
                replace h3 : -((k + 1) ^ (6 * m + t + 3) + k ^ (6 * m + t + 3)) ≡ -(-((k + 1) ^ (6 * m + t) - k ^ (6 * m + t))) [ZMOD T]:= by exact Int.neg_modEq_neg.mpr h3
                replace h2 : (k + 1) ^ (6 * (m + 1) + t) - k ^ (6 * (m + 1) + t) ≡ -(-((k + 1) ^ (6 * m + t) - k ^ (6 * m + t))) [ZMOD T]:= by exact Int.ModEq.trans h2 h3
                clear h3
                simp at h2
                replace h2 : (k + 1) ^ (6 * (m + 1) + t) - k ^ (6 * (m + 1) + t) - 1 ≡ (k + 1) ^ (6 * m + t) - k ^ (6 * m + t) - 1 [ZMOD T]:= by exact Int.ModEq.sub h2 rfl
                exact Int.ModEq.symm (Int.ModEq.trans (id (Int.ModEq.symm ih)) (id (Int.ModEq.symm h2)))

        -- Apply the result to our specific case based on the congruence of n modulo 6
        rcases h1 with h1 | h1
        .
            -- Case n ≡ 1 [MOD 6]: n = 6m + 1 for some m
            replace h1 : 6 ∣ n - 1:= by exact (Nat.modEq_iff_dvd' hn).mp (id (Nat.ModEq.symm h1))
            replace h1 : ∃ m : ℕ, n - 1 = 6 * m:= by exact h1
            rcases h1 with ⟨m, hm⟩
            replace hm : n = 6 * m + 1:= by omega
            specialize h2 1 (by simp) m
            subst n
            exact h2
        .
            -- Case n ≡ 5 [MOD 6]: n = 6m + 5 for some m
            replace h1 : 6 ∣ n - 5:= by exact (Nat.modEq_iff_dvd' h4).mp (id (Nat.ModEq.symm h1))
            replace h1 : ∃ m : ℕ, n - 5 = 6 * m:= by exact h1
            rcases h1 with ⟨m, hm⟩
            replace hm : n = 6 * m + 5:= by omega
            specialize h2 5 (by simp) m
            subst n
            exact h2
