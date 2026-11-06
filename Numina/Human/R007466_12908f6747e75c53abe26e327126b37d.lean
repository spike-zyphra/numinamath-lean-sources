import Mathlib
/- Let $p$ be an odd prime number and $a, b, c$ be integers so that the integers

$$
a^{2023}+b^{2023}, \quad b^{2024}+c^{2024}, \quad c^{2025}+a^{2025}
$$

are all divisible by $p$. Prove that $p$ divides each of $a, b$, and $c$. -/
theorem number_theory_607874 (p a b c : ℤ) (hp : Odd p ∧ Prime p) (h1 : p ∣ a ^ 2023 + b ^ 2023) (h2 : p ∣ b ^ 2024 + c^ 2024) (h3 : p ∣ c ^ 2025 + a ^ 2025) :
p ∣ a ∧ p ∣ b ∧ p ∣ c:= by
    -- Set k = 2023 for cleaner notation
    set k:= 2023 with hk
    -- Rewrite 2024 as k+1 and 2025 as k+2
    rw [show 2024 = k + 1 by ring] at h2
    rw [show 2025 = k + 2 by ring] at h3
    clear_value k
    -- Save original hypotheses for later use
    have g1:= h1
    have g2:= h2
    have g3:= h3
    -- Convert h1 to modular form: a^k + b^k ≡ 0 (mod p)
    replace h1 : a ^ k + b ^ k ≡ 0 [ZMOD p]:= by exact Int.ModEq.symm (Dvd.dvd.zero_modEq_int h1)
    -- Subtract b^k from both sides
    replace h1 : a ^ k + b ^ k - b ^ k ≡ 0 - b ^ k [ZMOD p]:= by exact Int.ModEq.sub h1 rfl
    ring_nf at h1
    -- Raise both sides to power (k+2)
    replace h1 : (a ^ k) ^ (k + 2) ≡ (-b ^ k) ^ (k + 2) [ZMOD p]:= by exact Int.ModEq.pow (k + 2) h1
    ring_nf at h1
    -- Establish that k is odd (2023 is odd)
    have hkodd : Odd k:= by rw [hk] ; decide
    -- Use the fact that (-1)^k = -1 when k is odd
    rw [show (-1 : ℤ) ^ k = -1 by exact Odd.neg_one_pow hkodd] at h1
    -- Simplify exponent expressions
    rw [show b ^ (k * 2) * b ^ (k ^ 2) = b ^ (k * (k + 2)) by ring] at h1
    rw [show a ^ (k * 2) * a ^ k ^ 2 = a ^ ((k + 2) * k) by ring] at h1
    rw [show a ^ ((k + 2) * k) = (a ^ (k + 2)) ^ k by ring] at h1
    -- Convert h3 to modular form: c^(k+2) + a^(k+2) ≡ 0 (mod p)
    replace h3 : c ^ (k + 2) + a ^ (k + 2) ≡ 0 [ZMOD p]:= by exact Int.ModEq.symm (Dvd.dvd.zero_modEq_int h3)
    -- Subtract c^(k+2) from both sides
    replace h3 : c ^ (k + 2) + a ^ (k + 2) - c ^ (k + 2) ≡ 0 - c ^ (k + 2) [ZMOD p]:= by exact Int.ModEq.sub h3 rfl
    ring_nf at h3
    -- Simplify exponent expressions
    rw [show a ^ 2 * a ^ k = a ^ (k + 2) by ring] at h3
    rw [show c ^ 2 * c ^ k = c ^ (k + 2) by ring] at h3
    -- Raise both sides to power k
    replace h3 : (a ^ (k + 2)) ^ k ≡ (-c ^ (k + 2)) ^ k [ZMOD p]:= by exact Int.ModEq.pow k h3
    rw [show (-c ^ (k + 2)) ^ k = (-1) ^ k * (c ^ (k + 2)) ^ k by ring] at h3
    rw [show (-1) ^ k = -1 by exact Odd.neg_one_pow hkodd] at h3
    -- Combine h1 and h3 through transitivity
    replace h1 : -1 * (c ^ (k + 2)) ^ k ≡ b ^ (k * (k + 2)) * -1 [ZMOD p]:= by exact Int.ModEq.trans (id (Int.ModEq.symm h3)) h1
    -- Multiply both sides by -1
    replace h1 : -1 * (c ^ (k + 2)) ^ k * (-1) ≡ b ^ (k * (k + 2)) * -1 * (-1) [ZMOD p]:= by exact Int.ModEq.mul h1 rfl
    ring_nf at h1
    clear h3
    -- Multiply both sides by c
    replace h1 : c ^ (k * 2) * c ^ k ^ 2 * c ≡ b ^ (k * 2) * b ^ k ^ 2 * c [ZMOD p]:= by exact Int.ModEq.mul h1 rfl
    rw [show c ^ (k * 2) * c ^ k ^ 2 * c = (c ^ (k + 1)) ^ (k + 1) by ring] at h1
    -- Convert h2 to modular form: b^(k+1) + c^(k+1) ≡ 0 (mod p)
    replace h2 : b ^ (k + 1) + c ^ (k + 1) ≡ 0 [ZMOD p]:= by exact Int.ModEq.symm (Dvd.dvd.zero_modEq_int h2)
    -- Subtract b^(k+1) from both sides
    replace h2 : b ^ (k + 1) + c ^ (k + 1) - b ^ (k + 1) ≡ 0 - b ^ (k + 1) [ZMOD p]:= by exact Int.ModEq.sub h2 rfl
    ring_nf at h2
    -- Simplify exponent expressions
    rw [show c * c ^ k = c ^ (k + 1) by ring] at h2
    rw [show b * b ^ k = b ^ (k + 1) by ring] at h2
    -- Raise both sides to power (k+1)
    replace h2 : (c ^ (k + 1)) ^ (k + 1) ≡ (-b ^ (k + 1)) ^ (k + 1) [ZMOD p]:= by exact Int.ModEq.pow (k + 1) h2
    -- Combine h1 and h2 through transitivity
    replace h1 : (-b ^ (k + 1)) ^ (k + 1) ≡ b ^ (k * 2) * b ^ k ^ 2 * c [ZMOD p]:= by exact Int.ModEq.trans (id (Int.ModEq.symm h2)) h1
    ring_nf at h1
    -- Use the fact that (-1)^k = -1 when k is odd
    rw [show (-1) ^ k = -1 by exact Odd.neg_one_pow hkodd] at h1
    ring_nf at h1
    -- Simplify expressions
    rw [show b * b ^ (k * 2) * b ^ k ^ 2 = b * b ^ (k * (k + 2)) by ring] at h1
    rw [show b ^ (k * 2) * b ^ k ^ 2 * c = c * b ^ (k * (k + 2)) by ring] at h1
    -- Convert back to divisibility form
    replace h1 : p ∣ b * b ^ (k * (k + 2)) - c * b ^ (k * (k + 2)):= by exact Int.ModEq.dvd (id (Int.ModEq.symm h1))
    -- Factor out the common term
    rw [show b * b ^ (k * (k + 2)) - c * b ^ (k * (k + 2)) = b ^ (k * (k + 2)) * (b - c) by ring] at h1
    -- Apply prime divisibility property: if p divides a product, it divides one of the factors
    replace h1 : p ∣ b ^ (k * (k + 2)) ∨ p ∣ b - c:= by refine Prime.dvd_or_dvd hp.2 h1
    -- Unpack the hypothesis about p being odd and prime
    rcases hp with ⟨hp1, hp2⟩
    clear h2
    -- Define a helper lemma: if p divides b, then p divides a, b, and c
    have h : p ∣ b → p ∣ a ∧ p ∣ b ∧ p ∣ c:= by
        intro h1
        -- If p divides b, then p divides b^k
        have h2 : p ∣ b ^ k:= by refine Dvd.dvd.pow h1 (by omega)
        -- From h1: p divides a^k + b^k, and p divides b^k, so p divides a^k
        replace g1 : p ∣ a ^ k:= by exact (Int.dvd_iff_dvd_of_dvd_add g1).mpr h2
        -- If p divides a^k, then p divides a (since p is prime)
        replace g1 : p ∣ a:= by exact Prime.dvd_of_dvd_pow hp2 g1
        -- If p divides b, then p divides b^(k+1)
        replace h2 : p ∣ b ^ (k + 1):= by refine Dvd.dvd.pow h1 (by omega)
        -- From g2: p divides b^(k+1) + c^(k+1), and p divides b^(k+1), so p divides c^(k+1)
        replace g2 : p ∣ c ^ (k + 1):= by exact (Int.dvd_iff_dvd_of_dvd_add g2).mp h2
        -- If p divides c^(k+1), then p divides c (since p is prime)
        replace g2 : p ∣ c:= by exact Prime.dvd_of_dvd_pow hp2 g2
        -- Combine the results
        exact ⟨g1, h1, g2⟩
    -- Handle the two cases from h1
    rcases h1 with h1 | h1
    -- Case 1: p divides b^(k*(k+2))
    .
        -- If p divides b^(k*(k+2)), then p divides b (since p is prime)
        replace h1 : p ∣ b:= by exact Prime.dvd_of_dvd_pow hp2 h1
        -- Apply the helper lemma
        exact h h1
    -- Case 2: p divides b-c
    .
        -- Convert to modular form: c ≡ b (mod p)
        replace h1 : c ≡ b [ZMOD p]:= by exact Int.modEq_iff_dvd.mpr h1
        -- If c ≡ b (mod p), then c^(k+1) ≡ b^(k+1) (mod p)
        replace h1 : c ^ (k + 1) ≡ b ^ (k + 1) [ZMOD p]:= by exact Int.ModEq.pow (k + 1) h1
        -- Convert back to divisibility form
        replace h1 : p ∣ b ^ (k + 1) - c ^ (k + 1):= by exact Int.ModEq.dvd h1
        -- Add g2: p divides b^(k+1) + c^(k+1)
        replace h1 : p ∣ (b ^ (k + 1) - c ^ (k + 1)) + (b ^ (k + 1) + c ^ (k + 1)):= by exact (Int.dvd_add_right h1).mpr g2
        -- Simplify the sum
        rw [show (b ^ (k + 1) - c ^ (k + 1)) + (b ^ (k + 1) + c ^ (k + 1)) = 2 * b ^ (k + 1) by ring] at h1
        -- Apply prime divisibility property: if p divides 2*b^(k+1), it divides 2 or b^(k+1)
        replace h1 : p ∣ 2 ∨ p ∣ b ^ (k + 1):= by refine Prime.dvd_or_dvd hp2 h1
        -- Handle the two subcases
        rcases h1 with h1 | h1
        -- Subcase 2.1: p divides 2
        .
            -- Convert to natural number divisibility
            replace h1 : p.natAbs ∣ 2:= by
                zify
                exact (abs_dvd p 2).mpr h1
            -- 2 is prime
            have g4 : Nat.Prime 2:= by norm_num
            -- If p.natAbs divides 2, then p.natAbs = 1 or p.natAbs = 2
            replace h1 : p.natAbs = 1 ∨ p.natAbs = 2:= by exact (Nat.dvd_prime g4).mp h1
            -- Handle the two possibilities
            rcases h1 with h1 | h1
            -- If p.natAbs = 1
            .
                zify at h1
                -- Then p = 1 or p = -1
                replace h1 : p = 1 ∨ p = -1:= by exact abs_eq_abs.mp h1
                rcases h1 with h1 | h1
                -- If p = 1, contradiction (p is not prime)
                .
                    subst p
                    omega
                -- If p = -1, contradiction (p is not prime)
                .
                    subst p
                    simp [Prime] at hp2
            -- If p.natAbs = 2
            .
                zify at h1
                -- Then p = 2 or p = -2
                replace h1 : p = 2 ∨ p = -2:= by exact abs_eq_abs.mp h1
                rcases h1 with h1 | h1
                -- In either case, p is even, contradicting the hypothesis that p is odd
                all_goals
                    have g5 : Even p:= by
                        subst p
                        decide
                    subst p
                    trivial
        -- Subcase 2.2: p divides b^(k+1)
        .
            -- If p divides b^(k+1), then p divides b (since p is prime)
            replace h1 : p ∣ b:= by exact Prime.dvd_of_dvd_pow hp2 h1
            -- Apply the helper lemma
            exact h h1
