import Mathlib
/- Let $a, b, c, d, e$ be distinct positive integers such that $a^{4}+b^{4}=c^{4}+d^{4}=e^{5}$. Show that $a c+b d$ is a composite number. -/
theorem number_theory_248831 (a b c d e : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) (hdist : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ b ≠ c ∧ b ≠ d ∧ b ≠ e ∧ c ≠ d ∧ c ≠ e ∧ d ≠ e) (h1 : a ^ 4 + b ^ 4 = e ^ 5) (h2 : c ^ 4 + d ^ 4 = e ^ 5) :
¬Prime (a * c + b * d):= by
    -- We use proof by contradiction
    by_contra H

    -- This helper lemma establishes an inequality that will be used in the main proof
    -- It shows that if ac+bd is prime, then ac+bd ≤ a²+d²
    have h3 : ∀ a b c d e : ℤ, a > 0 → b > 0 → c > 0 → d > 0 → e > 0 → a ≠ d → a ^ 4 + b ^ 4 = e ^ 5 → c ^ 4 + d ^ 4 = e ^ 5 → Prime (a * c + b * d) → a * c + b * d ≤ a ^ 2 + d ^ 2:= by
        intro a b c d e ha hb hc hd he hdist h1 h2 h3
        -- Define p as ac+bd for convenience
        set p:= a * c + b * d with hp
        clear_value p

        -- Since p divides itself, p ≡ 0 (mod p)
        have g1 : p ∣ p:= by simp
        replace g1 : p ≡ 0 [ZMOD p]:= by exact Dvd.dvd.modEq_zero_int g1
        replace g1 : a * c + b * d ≡ 0 [ZMOD p]:= by rw [←hp] ; exact g1

        -- Algebraic manipulations to isolate terms
        replace g1 : a * c + b * d - b * d ≡ 0 - b * d [ZMOD p]:= by exact Int.ModEq.sub g1 rfl
        ring_nf at g1
        apply Int.ModEq.pow 4 at g1
        ring_nf at g1

        -- Substitute using the original equations
        rw [show c ^ 4 = e ^ 5 - d ^ 4 by linarith] at g1
        rw [show b ^ 4 = e ^ 5 - a ^ 4 by linarith] at g1
        ring_nf at g1

        -- More algebraic manipulations
        replace g1 : a ^ 4 * e ^ 5 - a ^ 4 * d ^ 4 + a ^ 4 * d ^ 4 ≡ -(a ^ 4 * d ^ 4) + e ^ 5 * d ^ 4 + a ^ 4 * d ^ 4 [ZMOD p]:= by exact Int.ModEq.add g1 rfl
        ring_nf at g1

        -- Derive that p divides a^4*e^5 - e^5*d^4
        replace g1 : p ∣ a ^ 4 * e ^ 5 - e ^ 5 * d ^ 4:= by exact Int.ModEq.dvd (id (Int.ModEq.symm g1))

        -- Factor the expression
        rw [show a ^ 4 * e ^ 5 - e ^ 5 * d ^ 4 = e ^ 5 * (a - d) * (a + d) * (a ^ 2 + d ^ 2) by ring] at g1

        -- Prove that p > e
        have h4 : p > e:= by
            by_contra H
            simp at H
            have h4 : p ≥ 0:= by rw [hp] ; positivity
            replace H : p ^ 5 ≤ e ^ 5:= by exact pow_le_pow_left h4 H 5

            -- Series of inequalities to reach a contradiction
            have g2 : a ^ 4 ≤ a ^ 5:= by refine pow_le_pow_right₀ ha (by linarith)
            have g3 : b ^ 4 ≤ b ^ 5:= by refine pow_le_pow_right₀ hb (by linarith)
            have g4 : a * c ≥ a:= by exact (le_mul_iff_one_le_right ha).mpr hc
            have g5 : b * d ≥ b:= by exact (le_mul_iff_one_le_right hb).mpr hd
            replace g4 : p ≥ a + b:= by linarith
            clear g5
            replace g4 : p ^ 5 ≥ (a + b) ^ 5:= by exact pow_le_pow_left (by positivity) (by linarith) 5
            replace H : p ^ 5 ≤ a ^ 5 + b ^ 5:= by linarith
            clear g2 g3

            -- Show that (a+b)^5 > a^5+b^5 for positive a,b
            have g6 : (a + b) ^ 5 - a ^ 5 - b ^ 5 > 0:= by
                ring_nf
                positivity
            linarith

        -- Establish that p is positive
        have h5 : p > 0:= by rw [hp] ; positivity

        -- If p divides a positive integer k, then k ≥ p
        have h6 : ∀ k : ℤ, k > 0 → p ∣ k → k ≥ p:= by
            intro k hk g1
            replace g1 : ∃ t : ℤ, k = p * t:= by exact g1
            rcases g1 with ⟨t, ht⟩
            have ht1 : t > 0:= by
                by_contra H
                simp at H
                replace H : -t ≥ 0:= by linarith
                replace H : p * (-t) ≥ 0:= by positivity
                linarith
            replace ht1 : p * t ≥ p:= by exact (le_mul_iff_one_le_right h5).mpr ht1
            linarith

        -- Prove that p > |a-d|
        have h7 : p > |a - d|:= by
            have h7 : |a - d| < a + d:= by
                by_cases h7 : a - d ≥ 0
                .
                    rw [abs_of_nonneg h7]
                    linarith
                .
                    simp at h7
                    rw [show |a - d| = |d - a| by exact abs_sub_comm a d]
                    replace h7 : d - a > 0:= by linarith
                    rw [abs_of_pos h7]
                    linarith
            have g2 : a * c ≥ a:= by exact (le_mul_iff_one_le_right ha).mpr hc
            have g3 : b * d ≥ d:= by exact (le_mul_iff_one_le_left hd).mpr hb
            linarith

        -- Since p is prime and divides a product, it must divide one of the factors
        apply Prime.dvd_or_dvd h3 at g1
        rcases g1 with g1 | g1
        .
            apply Prime.dvd_or_dvd h3 at g1
            rcases g1 with g1 | g1
            .
                apply Prime.dvd_or_dvd h3 at g1
                rcases g1 with g1 | g1
                .
                    -- Case: p divides e
                    replace g1 : p ∣ e:= by exact Prime.dvd_of_dvd_pow h3 g1
                    specialize h6 e he g1
                    linarith
                .
                    -- Case: p divides |a-d|
                    replace g1 : p ∣ |a - d|:= by exact (dvd_abs p (a - d)).mpr g1
                    replace hdist : a - d ≠ 0:= by exact sub_ne_zero_of_ne hdist
                    replace hdist : |a - d| > 0:= by exact abs_pos.mpr hdist
                    specialize h6 (|a - d|) hdist g1
                    linarith
            .
                -- Case: p divides a+d
                specialize h6 (a + d) (by positivity) g1
                have g2 : a ^ 2 ≥ a:= by exact Int.le_self_sq a
                have g3 : d ^ 2 ≥ d:= by exact Int.le_self_sq d
                linarith
        .
            -- Case: p divides a²+d²
            specialize h6 (a ^ 2 + d ^ 2) (by positivity) g1
            exact h6

    -- Apply the helper lemma with swapped variables
    have h4:= h3 b a d c e hb ha hd hc he (hdist.2.2.2.2.1) (by linarith) (by linarith) (by rw [show b * d + a * c = a * c + b * d by ring] ; exact H)

    -- Apply the helper lemma with original variables
    specialize h3 a b c d e ha hb hc hd he (hdist.2.2.1) h1 h2 H

    -- Derive inequalities from the helper lemma applications
    replace h4 : b * (b - d) ≥ c * (a - c):= by linarith
    replace h3 : a * (a - c) ≥ d * (b - d):= by linarith

    -- From the original equations, derive a key relationship
    rw [←h2] at h1
    replace h1 : (a - c) * (a + c) * (a ^ 2 + c ^ 2) = (d - b) * (d + b) * (d ^ 2 + b ^ 2):= by linarith

    -- Case analysis on whether a-c is non-negative
    by_cases h5 : a - c ≥ 0
    .
        -- Case: a-c ≥ 0
        replace hdist:= hdist.2.1
        replace hdist: a - c ≠ 0:= by exact sub_ne_zero_of_ne hdist
        replace h5 : a - c > 0:= by omega

        -- Show that d-b > 0
        have h6 : d - b > 0:= by
            by_contra H
            simp at H
            replace H : b - d ≥ 0:= by linarith
            replace H : (b - d) * (d + b) * (d ^ 2 + b ^ 2) ≥ 0:= by positivity
            replace h5 : (a - c) * (a + c) * (a ^ 2 + c ^ 2) > 0:= by positivity
            linarith

        -- Derive a contradiction from the inequalities
        replace h5 : c * (a - c) > 0:= by positivity
        replace h6 : b * (d - b) > 0:= by positivity
        linarith
    .
        -- Case: a-c < 0
        simp at h5
        replace h5 : c - a > 0:= by omega

        -- Show that b-d > 0
        have h7 : b - d > 0:= by
            by_contra H
            simp at H
            replace H : d - b ≥ 0:= by linarith
            replace H : (d - b) * (d + b) * (d ^ 2 + b ^ 2) ≥ 0:= by positivity
            replace h5 : (c - a) * (a + c) * (a ^ 2 + c ^ 2) > 0:= by positivity
            linarith

        -- Derive a contradiction from the inequalities
        replace h5 : a * (c - a) > 0:= by positivity
        replace h7 : d * (b - d) > 0:= by positivity
        linarith
