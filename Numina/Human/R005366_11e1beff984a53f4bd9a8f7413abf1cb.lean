import Mathlib
/-For positive real numbers $a, b, c$, which of the following statements necessarily implies $a=b=c$ : (I) $a\left(b^{3}+c^{3}\right)=b\left(c^{3}+a^{3}\right)=c\left(a^{3}+b^{3}\right)$, (II) $a\left(a^{3}+b^{3}\right)=b\left(b^{3}+c^{3}\right)=c\left(c^{3}+a^{3}\right)$ ? Justify your answer. -/
theorem algebra_607909 : (∃ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a ≠ b ∨ b ≠ c ∧ ((c * (a ^ 3 + b ^ 3) = a * (b ^ 3 + c ^ 3)) ∧ (a * (b ^ 3 + c ^ 3) = b * (c ^ 3 + a ^ 3)))) ∧ (∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a * (a ^ 3 + b ^ 3) = b * (b ^ 3 + c ^ 3) ∧ (b * (b ^ 3 + c ^ 3) = c * (c ^ 3 + a ^ 3)) → a = b ∧ b = c):= by
    constructor
    -- Part 1: Proving existence of counterexample
    -- Using values a=2, b=2, c=-1+√5
    .
        use 2
        use 2
        use (-1 + √5)
        simp
        ring_nf
        norm_num
        rw [show √5 ^ 3 = √5 * √5 ^ 2 by ring]
        norm_num
        ring_nf
        simp
        by_contra H
        replace H : 3 = √5:= by linarith
        replace H : 3 ^ 2 = √5 ^ 2:= by rw [H]
        norm_num at H

    -- Part 2: Proving the second system forces equality
    .
        intro a b c ⟨ha, hb, hc, h1, h2⟩
        -- Helper lemma: if one number is greater than or equal to the other two, then all are equal
        have h3 : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a * (a ^ 3 + b ^ 3) = b * (b ^ 3 + c ^ 3) ∧ (b * (b ^ 3 + c ^ 3) = c * (c ^ 3 + a ^ 3)) ∧ (a ≥ b) ∧ (a ≥ c) → a = b ∧ b = c:= by
            intro a b c ⟨ha, hb, hc, h1, _, h3, h4⟩
            -- Proving key inequalities using positivity
            have g1 : (a ^ 3 + b ^ 3) * (a - b) ≥ 0:= by
                replace h3 : a - b ≥ 0:= by linarith
                positivity
            have g2 : b * (a ^ 2 + c ^ 2 + (a + c) ^ 2) * (a - c) ≥ 0:= by
                replace h4 : a - c ≥ 0:= by linarith
                positivity
            replace g1 : (a ^ 3 + b ^ 3) * (a - b) = 0:= by linarith
            replace g2 : b * (a ^ 2 + c ^ 2 + (a + c) ^ 2) * (a - c) = 0:= by linarith
            have g3 : a ^ 3 + b ^ 3 ≠ 0:= by positivity
            have g4 : b * (a ^ 2 + c ^ 2 + (a + c) ^ 2) ≠ 0:= by positivity
            replace g1 : a - b = 0:= by exact eq_zero_of_ne_zero_of_mul_left_eq_zero g3 g1
            replace g2 : a - c = 0:= by exact eq_zero_of_ne_zero_of_mul_left_eq_zero g4 g2
            constructor
            all_goals
            linarith

        -- Proving that one of the three numbers must be greater than or equal to the other two
        have h4 : (a ≥ b ∧ a ≥ c) ∨ (b ≥ a ∧ b ≥ c) ∨ (c ≥ a ∧ c ≥ b):= by
            by_contra H
            simp at H
            rcases H with ⟨H1, H2, H3⟩
            by_cases h4 : b ≤ a
            .
                replace H1:= H1 (by linarith)
                replace H3:= H3 (by linarith)
                linarith
            .
                simp at h4
                replace H2:= H2 (by linarith)
                replace H3:= H3 (by linarith)
                linarith

        -- Applying the helper lemma to each possible case
        rcases h4 with h4 | h4 | h4
        .
            specialize h3 a b c ⟨ha, hb, hc, h1, h2, h4⟩
            exact h3
        .
            specialize h3 b c a ⟨hb, hc, ha, (by linarith), (by linarith), (by linarith), (by linarith)⟩
            rcases h3 with ⟨h3, h4⟩
            constructor
            all_goals
            linarith
        .
            specialize h3 c a b ⟨hc, ha, hb, (by linarith), (by linarith), h4⟩
            rcases h3 with ⟨h3, h4⟩
            constructor
            all_goals
            linarith
