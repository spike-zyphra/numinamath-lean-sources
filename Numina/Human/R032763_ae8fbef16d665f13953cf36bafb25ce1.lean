import Mathlib
/- Trouver tous les triplets de réels positifs ou nuls ( $\mathrm{a}, \mathrm{b}, \mathrm{c})$ tels que

$$
\left\{\begin{array}{l}
a^{2}+a b=c \\
b^{2}+b c=a \\
c^{2}+c a=b
\end{array}\right.
$$ -/
theorem algebra_607358 (a b c : ℝ) :
    a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ a ^ 2 + a * b = c ∧ b ^ 2 + b * c = a ∧ c ^ 2 + c * a = b ↔
    (a = 0 ∧ b = 0 ∧ c = 0) ∨ (a = 1 / 2 ∧ b = 1 / 2 ∧ c = 1 / 2) := by
        constructor
        .
        -- Forward direction: proving that the equations imply the solutions
            intro h
            rcases h with ⟨ha, hb, hc, h1, h2, h3⟩
            by_cases hpos : a = 0 ∨ b = 0 ∨ c = 0
            .
            -- Case 1: At least one variable is zero
                left
                rcases hpos with hpos | hpos | hpos
                .
                -- Subcase 1.1: When a = 0, prove b = c = 0
                    rw [hpos] at h2
                    subst a
                    simp at h1
                    subst c
                    simp at h3
                    subst b
                    simp
                .
                -- Subcase 1.2: When b = 0, prove a = c = 0
                    rw [hpos] at h3
                    subst b
                    simp at h2
                    subst a
                    simp at h1
                    subst c
                    simp
                .
                -- Subcase 1.3: When c = 0, prove a = b = 0
                    rw [hpos] at h1
                    subst c
                    simp at h2
                    subst b
                    simp at h1
                    subst a
                    simp
            .
            -- Case 2: All variables are strictly positive
                simp at hpos
                rcases hpos with ⟨hapos, hbpos, hcpos⟩
                right
                by_cases heq : a = b ∨ b = c ∨ c = a
                .
                -- Subcase 2.1: At least two variables are equal
                    rcases heq with heq | heq | heq
                    .
                    -- When a = b, prove all variables equal 1/2
                        rw [heq] at h2 h3
                        have h4 : (b + c) * (b - c) = 0:= by linarith
                        have h5 : b + c ≠ 0:= by positivity
                        replace h4 : b - c = 0:= by exact eq_zero_of_ne_zero_of_mul_left_eq_zero h5 h4
                        replace h4 : b = c:= by linarith
                        rw [heq, h4] at h1
                        replace h1 : c * (2 * c - 1) = 0:= by linarith
                        replace h1 : 2 * c - 1 = 0:= by exact eq_zero_of_ne_zero_of_mul_left_eq_zero hcpos h1
                        replace h1 : c = 1 / 2:= by linarith
                        subst c b a
                        simp
                    .
                    -- When b = c, prove all variables equal 1/2
                        rw [heq] at h3 h1
                        have h4 : (c + a) * (c - a) = 0:= by linarith
                        have h5 : c + a ≠ 0:= by positivity
                        replace h4 : c - a = 0:= by exact eq_zero_of_ne_zero_of_mul_left_eq_zero h5 h4
                        replace h4 : c = a:= by linarith
                        rw [heq, h4] at h2
                        replace h2 : a * (2 * a - 1) = 0:= by linarith
                        replace h2 : 2 * a - 1 = 0:= by exact eq_zero_of_ne_zero_of_mul_left_eq_zero hapos h2
                        replace h2 : a = 1 / 2:= by linarith
                        subst a b c
                        simp
                    .
                    -- When c = a, prove all variables equal 1/2
                        rw [heq] at h1 h2
                        have h4 : (a + b) * (a - b) = 0:= by linarith
                        have h5 : a + b ≠ 0:= by positivity
                        replace h4 : a - b = 0:= by exact eq_zero_of_ne_zero_of_mul_left_eq_zero h5 h4
                        replace h4 : a = b:= by linarith
                        rw [heq, h4] at h3
                        replace h3 : b * (2 * b - 1) = 0:= by linarith
                        replace h3 : 2 * b - 1 = 0:= by exact eq_zero_of_ne_zero_of_mul_left_eq_zero hbpos h3
                        replace h3 : b = 1 / 2:= by linarith
                        subst a b c
                        simp
                .
                -- Subcase 2.2: All variables are different
                    simp at heq
                    rcases heq with ⟨hneq1, hneq2, hneq3⟩
                    -- Rewrite equations in factored form
                    rw [show a ^ 2 + a * b = a * (a + b) by ring] at h1
                    rw [show b ^ 2 + b * c = b * (b + c) by ring] at h2
                    rw [show c ^ 2 + c * a = c * (c + a) by ring] at h3
                    -- Derive contradiction through algebraic manipulation
                    have h4 : a * (a + b) * (b * (b + c)) * (c * (c + a)) = c * a * b:= by rw [h1, h2, h3]
                    replace h4 : a * b * c * ((a + b) * (b + c) * (c + a) - 1) = 0:= by linarith
                    have h5 : a * b * c ≠ 0:= by positivity
                    replace h4 : (a + b) * (b + c) * (c + a) - 1 = 0:= by exact eq_zero_of_ne_zero_of_mul_left_eq_zero h5 h4
                    replace h4 : (a + b) * (b + c) * (c + a) = 1:= by linarith
                    have h6 : (a - b) * (a + b) = (c - a) * (b + 1):= by linarith
                    have h7 : (b - c) * (b + c) = (a - b) * (c + 1):= by linarith
                    have h8 : (c - a) * (c + a) = (b - c) * (a + 1):= by linarith
                    have h9 : (a - b) * (a + b) * ((b - c) * (b + c)) * ((c - a) * (c + a)) = (c - a) * (b + 1) * ((a - b) * (c + 1)) * ((b - c) * (a + 1)):= by rw [h6, h7, h8]
                    replace h9 : (a - b) * (b - c) * (c - a) * ((a + b) * (b + c) * (c + a) - (a + 1) * (b + 1) * (c + 1)) = 0:= by linarith
                    -- Prove that this case leads to contradiction
                    have h10 : (a - b) * (b - c) * (c - a) ≠ 0:= by
                        by_contra H
                        replace H : (a - b) * (b - c) = 0 ∨ c - a = 0:= by exact mul_eq_zero.mp H
                        rcases H with H | H
                        .
                            replace H : a - b = 0 ∨ b - c = 0:= by exact mul_eq_zero.mp H
                            rcases H with H | H
                            .
                                replace H : a = b:= by linarith
                                trivial
                            .
                                replace H : b = c:= by linarith
                                trivial
                        .
                            replace H : c = a:= by linarith
                            trivial
                    replace h9 : (a + b) * (b + c) * (c + a) - (a + 1) * (b + 1) * (c + 1) = 0:= by exact eq_zero_of_ne_zero_of_mul_left_eq_zero h10 h9
                    rw [h4] at h9
                    ring_nf at h9
                    replace h10 : a + ((a * b) + a * b * c) + ((a * c) + b) + ((b * c) + c) > 0:= by positivity
                    by_contra _
                    linarith
        .
        -- Backward direction: proving that the solutions satisfy the equations
            intro h
            rcases h with h | h
            all_goals
                rcases h with ⟨ha, hb, hc⟩
                subst a b c
                simp
            ring_nf
