import Mathlib
/- Soient $p$ et $q$ deux nombres premiers supérieurs ou égaux à 7 . Soit $x=\frac{p^{2012}+q^{2016}}{120}$. Calculer $x-[x]$, où $[x]$ désigne la partie entière de $x$, c'est-à-dire le plus grand entier inférieur ou égal à $x$. -/
theorem number_theory_607593 (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (h : p ≥ 7 ∧ q ≥ 7) :
((p ^ 2012 + q ^ 2016) / 120 : ℝ) - ⌊((p ^ 2012 + q ^ 2016) / 120 : ℝ)⌋ = 1 / 60 := by
    -- Key lemma: For any natural number a not divisible by 2, 3, or 5,
    -- a^4 ≡ 1 (mod 120)
    have h1 : ∀ a : ℕ, ¬(2 ∣ a ∨ 3 ∣ a ∨ 5 ∣ a) → a ^ 4 ≡ 1 [MOD 120]:= by
        intro a ha
        simp at ha
        rcases ha with ⟨h1, h2, h3⟩
        -- Ensure a ≥ 1
        have g1 : a ≥ 1:= by
            by_contra H
            simp at H
            subst a
            simp at h1
        -- Set b = a - 1 to rewrite a^4 in a more convenient form
        set b:= a - 1 with hb
        clear_value b
        replace hb : a = b + 1:= by omega
        subst a
        ring_nf
        -- Rewrite (b+1)^4 as b*(b+2)*((b+1)^2+1) + 1
        rw [show 1 + b * 4 + b ^ 2 * 6 + b ^ 3 * 4 + b ^ 4 = b * (b + 2) * ((b + 1) ^ 2 + 1) + 1 by linarith]
        -- Prove that b*(b+2)*((b+1)^2+1) ≡ 0 (mod 120)
        have h4 : b * (b + 2) * ((b + 1) ^ 2 + 1) ≡ 0 [MOD 120]:= by
            suffices 120 ∣ b * (b + 2) * ((b + 1) ^ 2 + 1) by exact Nat.modEq_zero_iff_dvd.mpr this
            -- Factorize 120 = 3 * 5 * 8
            rw [show 120 = 3 * 5 * 8 by ring]
            zify
            zify at h2 h3
            replace h1 : ¬(2 ∣ b + 1):= by simp ; exact h1
            zify at h1
            -- Set c = b + 1 for cleaner expressions
            set c:= (↑b : ℤ) + 1 with hc
            clear_value c
            replace hc : b = c - 1:= by omega
            rw [hc]
            rw [show c - 1 + 2 = c + 1 by ring]
            -- Prove that 3 divides (c-1)*(c+1)*(c^2+1)
            replace g1 : 3 ∣ (c - 1) * (c + 1) * (c ^ 2 + 1):= by
                mod_cases c % 3
                .
                    replace H : 3 ∣ c:= by exact Int.dvd_of_emod_eq_zero H
                    trivial
                .
                    replace H : 3 ∣ c - 1:= by exact Int.dvd_sub_of_emod_eq H
                    rw [show (c - 1) * (c + 1) * (c ^ 2 + 1) = (c - 1) * ((c + 1) * (c ^ 2 + 1)) by ring]
                    exact Dvd.dvd.mul_right H ((c + 1) * (c ^ 2 + 1))
                .
                    replace H : c ≡ -1 [ZMOD 3]:= by exact H
                    replace H : 3 ∣ c - (-1):= by exact Int.ModEq.dvd (id (Int.ModEq.symm H))
                    ring_nf at H
                    rw [show 1 + c = c + 1 by ring] at H
                    rw [show (c - 1) * (c + 1) * (c ^ 2 + 1) = (c + 1) * ((c - 1) * (c ^ 2 + 1)) by ring]
                    exact Dvd.dvd.mul_right H ((c - 1) * (c ^ 2 + 1))
            -- Prove that 5 divides (c-1)*(c+1)*(c^2+1)
            have g2 : 5 ∣ (c - 1) * (c + 1) * (c ^ 2 + 1):= by
                mod_cases c % 5
                .
                    replace H : 5 ∣ c:= by exact Int.dvd_of_emod_eq_zero H
                    trivial
                .
                    replace H : 5 ∣ c - 1:= by exact Int.dvd_sub_of_emod_eq H
                    rw [show (c - 1) * (c + 1) * (c ^ 2 + 1) = (c - 1) * ((c + 1) * (c ^ 2 + 1)) by ring]
                    exact Dvd.dvd.mul_right H ((c + 1) * (c ^ 2 + 1))
                .
                    replace H : c ^ 2 ≡ 2 ^ 2 [ZMOD 5]:= by exact Int.ModEq.pow 2 H
                    replace H : c ^ 2 ≡ -1 [ZMOD 5]:= by exact H
                    replace H : 5 ∣ c ^ 2 - (-1):= by exact Int.ModEq.dvd (id (Int.ModEq.symm H))
                    simp at H
                    exact Dvd.dvd.mul_left H ((c - 1) * (c + 1))
                .
                    replace H : c ^ 2 ≡ 3 ^ 2 [ZMOD 5]:= by exact Int.ModEq.pow 2 H
                    replace H : c ^ 2 ≡ -1 [ZMOD 5]:= by exact H
                    replace H : 5 ∣ c ^ 2 - (-1):= by exact Int.ModEq.dvd (id (Int.ModEq.symm H))
                    simp at H
                    exact Dvd.dvd.mul_left H ((c - 1) * (c + 1))
                .
                    replace H : c ≡ -1 [ZMOD 5]:= by exact H
                    replace H : 5 ∣ c - (-1):= by exact Int.ModEq.dvd (id (Int.ModEq.symm H))
                    simp at H
                    rw [show (c - 1) * (c + 1) * (c ^ 2 + 1) = (c + 1) * ((c - 1) * (c ^ 2 + 1)) by ring]
                    exact Dvd.dvd.mul_right H ((c - 1) * (c ^ 2 + 1))
            -- Prove that 8 divides (c-1)*(c+1)*(c^2+1)
            have g3 : 8 ∣ (c - 1) * (c + 1) * (c ^ 2 + 1):= by
                replace h1 : Odd c:= by
                    by_contra H
                    simp at H
                    replace H : 2 ∣ c:= by exact even_iff_two_dvd.mp H
                    trivial
                simp [Odd] at h1
                rcases h1 with ⟨k, hk⟩
                subst c
                rw [show (2 * k + 1 - 1) * (2 * k + 1 + 1) * ((2 * k + 1) ^ 2 + 1) = k * (k + 1) * (2 * k ^ 2 + 2 * k + 1) * 8 by ring]
                simp
            -- Combine the divisibility results to show 120 divides the expression
            have g4 : IsCoprime (3 : ℤ) 5:= by norm_num
            replace g1 : 3 * 5 ∣ (c - 1) * (c + 1) * (c ^ 2 + 1):= by exact IsCoprime.mul_dvd g4 g1 g2
            rw [show (3 : ℤ) * 5 = 15 by ring] at g1
            have g5 : IsCoprime (15 : ℤ) 8:= by norm_num
            replace g1 : 15 * 8 ∣ (c - 1) * (c + 1) * (c ^ 2 + 1):= by exact IsCoprime.mul_dvd g5 g1 g3
            simp at g1
            simp
            exact g1
        -- Complete the proof of the lemma
        replace h4 : b * (b + 2) * ((b + 1) ^ 2 + 1) + 1 ≡ 0 + 1 [MOD 120]:= by exact Nat.ModEq.add_right 1 h4
        simp at h4
        exact h4

    -- Extract the conditions from the hypothesis
    rcases h with ⟨hp1, hq1⟩

    -- Prove that p is not divisible by 2, 3, or 5
    have hp2 : ¬(2 ∣ p ∨ 3 ∣ p ∨ 5 ∣ p):= by
        by_contra H
        have g1 : Nat.Prime 2:= by norm_num
        have g2 : Nat.Prime 3:= by norm_num
        have g3 : Nat.Prime 5:= by norm_num
        rcases H with H | H | H
        .
            replace H : 2 = p:= by exact (Nat.prime_dvd_prime_iff_eq g1 hp).mp H
            linarith
        .
            replace H : 3 = p:= by exact (Nat.prime_dvd_prime_iff_eq g2 hp).mp H
            linarith
        .
            replace H : 5 = p:= by exact (Nat.prime_dvd_prime_iff_eq g3 hp).mp H
            linarith

    -- Prove that q is not divisible by 2, 3, or 5
    have hq2 : ¬(2 ∣ q ∨ 3 ∣ q ∨ 5 ∣ q):= by
        by_contra H
        have g1 : Nat.Prime 2:= by norm_num
        have g2 : Nat.Prime 3:= by norm_num
        have g3 : Nat.Prime 5:= by norm_num
        rcases H with H | H | H
        .
            replace H : 2 = q:= by exact (Nat.prime_dvd_prime_iff_eq g1 hq).mp H
            linarith
        .
            replace H : 3 = q:= by exact (Nat.prime_dvd_prime_iff_eq g2 hq).mp H
            linarith
        .
            replace H : 5 = q:= by exact (Nat.prime_dvd_prime_iff_eq g3 hq).mp H
            linarith

    -- Apply the lemma to p and q
    have h2:= h1 q hq2
    replace h1:= h1 p hp2

    -- Define constants for the exponents
    set m:= 503 with hm
    clear_value m
    apply Nat.ModEq.pow 503 at h1
    apply Nat.ModEq.pow 504 at h2
    set t:= 503 with ht
    set s:= 504 with hs
    clear_value t s
    simp at h1 h2
    ring_nf at h1 h2

    -- Rewrite the exponents 2012 and 2016 in terms of t and s
    rw [show 2012 = t * 4 by omega]
    rw [show 2016 = s * 4 by omega]

    -- Establish lower bounds for the powers
    have h3 : p ^ (t * 4) ≥ 1:= by
        by_contra H
        simp at H
        replace H:= H.1
        linarith
    have h4 : q ^ (s * 4) ≥ 1:= by
        by_contra H
        simp at H
        replace H:= H.1
        linarith

    -- Convert congruences to divisibility statements
    replace h1 : 120 ∣ p ^ (t * 4) - 1:= by exact (Nat.modEq_iff_dvd' h3).mp (id (Nat.ModEq.symm h1))
    replace h2 : 120 ∣ q ^ (s * 4) - 1:= by exact (Nat.modEq_iff_dvd' h4).mp (id (Nat.ModEq.symm h2))
    replace h1 : ∃ a : ℕ, p ^ (t * 4) - 1 = 120 * a:= by exact h1
    replace h2 : ∃ b : ℕ, q ^ (s * 4) - 1 = 120 * b:= by exact h2
    rcases h1 with ⟨a, ha⟩
    rcases h2 with ⟨b, hb⟩
    replace ha : p ^ (t * 4) = 120 * a + 1:= by omega
    replace hb : q ^ (s * 4) = 120 * b + 1:= by omega
    clear h3 h4

    -- Convert to real numbers and compute the final result
    rify at ha hb
    rw [ha, hb]
    rw [show (120 * (↑a : ℝ) + 1 + (120 * ↑b + 1)) / 120 = a + b + 1 / 60 by linarith]
    rw [show ⌊(↑a : ℝ) + ↑b + 1 / 60⌋ = a + b by refine Int.floor_eq_iff.mpr ⟨(by norm_cast ; linarith), (by norm_cast ; simp ; norm_num)⟩]
    simp
