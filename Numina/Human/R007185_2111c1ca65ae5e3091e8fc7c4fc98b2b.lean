import Mathlib
/- Find all triples $(a, b, c)$ of real numbers such that the following system holds:

$$
\left\{\begin{array}{l}
a+b+c=\frac{1}{a}+\frac{1}{b}+\frac{1}{c} \\
a^{2}+b^{2}+c^{2}=\frac{1}{a^{2}}+\frac{1}{b^{2}}+\frac{1}{c^{2}}
\end{array}\right.
$$ -/
theorem algebra_605533 : {(a, b, c) : ℝ × ℝ × ℝ | a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ a + b + c = 1 / a + 1 / b + 1 / c ∧ a ^ 2 + b ^ 2 + c ^ 2 = 1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2} = {(a, b, c) : ℝ × ℝ × ℝ | ∃ t : ℝ, t ≠ 0 ∧ ((a, b, c) = (t, 1 / t, 1) ∨ (a, b, c) = (t, 1, 1 / t) ∨ (a, b, c) = (1, t, 1 / t) ∨ (a, b, c) = (1 / t, t, -1) ∨ (a, b, c) = (t, -1, 1 / t) ∨ (a, b, c) = (-1, t, 1 / t))}:= by
    ext ⟨a, b, c⟩
    constructor
    .
        intro h
        simp at h
        rcases h with ⟨h1, h2, h3, h4, h5⟩
        -- Key lemma: if abc > 0 and the equations hold, then one value is 1 and others are t and 1/t
        have h6 : ∀ a b c : ℝ, a ≠ 0 → b ≠ 0 → c ≠ 0 → a + b + c = a⁻¹ + b⁻¹ + c⁻¹ → a ^ 2 + b ^ 2 + c ^ 2 = (a ^ 2)⁻¹ + (b ^ 2)⁻¹ + (c ^ 2)⁻¹ → a * b * c > 0 → ∃ t : ℝ, t ≠ 0 ∧ ((a = t ∧ b = 1 / t ∧ c = 1) ∨ (a = t ∧ b = 1 ∧ c = 1 / t) ∨ (a = 1 ∧ b = t ∧ c = 1 / t)):= by
            intro a b c ha hb hc h1 h2 h3
            field_simp at h1 h2
            -- Prove that ab + bc + ca ≠ 0 by contradiction
            have g1 : a * b + b * c + c * a ≠ 0:= by
                by_contra H
                replace h1 : (a + b + c) * (a * b * c) = 0:= by linarith
                replace h3 : a * b * c ≠ 0:= by linarith
                simp [h3] at h1
                replace h1 : (a + b + c) ^ 2 = 0:= by rw [h1] ; simp
                replace h1 : a ^ 2 + b ^ 2 + c ^ 2 = 0:= by linarith
                have g1 : a ^ 2 ≥ 0:= by positivity
                have g2 : b ^ 2 ≥ 0:= by positivity
                have g3 : c ^ 2 ≥ 0:= by positivity
                replace g1 : a ^ 2 = 0:= by linarith
                simp at g1
                trivial
            -- Key equation from the first condition
            have h4 : ((a + b + c) * (a * b * c)) ^ 2 = ((b + a) * c + a * b) ^ 2:= by rw [h1]
            -- Manipulate equations to show abc = 1
            replace h2 : (a * b + b * c + c * a) * (a * b * c) ^ 2 = (a + b + c) * (a * b * c):= by linarith
            rw [h1] at h2
            replace h2 : (a * b + b * c + c * a) * ((a * b * c) ^ 2 - 1) = 0:= by linarith
            simp [g1] at h2
            replace h2 : (a * b * c - 1) * (a * b * c + 1) = 0:= by linarith
            have g2 : a * b * c + 1 ≠ 0:= by positivity
            simp [g2] at h2
            replace h2 : a * b * c = 1:= by linarith
            clear g1 g2 h4 h3
            -- Show that one of a, b, or c must be 1
            rw [h2] at h1
            replace h1 : (a - 1) * (b - 1) * (c - 1) = 0:= by linarith
            simp at h1
            rcases h1 with ⟨h1 | h1⟩ | h1
            -- Handle the three cases where a=1, b=1, or c=1
            .
                replace h1 : a = 1:= by linarith
                subst a
                simp at h2
                use b
                refine ⟨hb, ?_⟩
                right
                right
                simp
                field_simp
                linarith
            .
                replace h1 : b = 1:= by linarith
                subst b
                simp at h2
                use a
                refine ⟨ha, ?_⟩
                right
                left
                simp
                field_simp
                linarith
            .
                replace h1 : c = 1:= by linarith
                subst c
                simp at h2
                use a
                refine ⟨ha, ?_⟩
                left
                simp
                field_simp
                linarith
        -- Check if the product abc is non-zero
        have g1 : a * b * c ≠ 0:= by positivity
        -- Split into two cases: abc < 0 or abc > 0
        replace g1 : a * b * c < 0 ∨ a * b * c > 0:= by exact lt_or_gt_of_ne g1
        rcases g1 with g1 | g1
        .
            -- Case 1: abc < 0
            -- Apply lemma h6 to (-a, -b, -c) to handle negative case
            specialize h6 (-a) (-b) (-c) (by exact neg_ne_zero.mpr h1) (by exact neg_ne_zero.mpr h2) (by exact neg_ne_zero.mpr h3) (by field_simp ; ring_nf ; field_simp ; field_simp at h4 ; linarith) (by field_simp ; ring_nf ; field_simp at h5 ; linarith) (by linarith)
            rcases h6 with ⟨t, ht, h6⟩
            -- Ensure -t is non-zero
            have ht1 : -t ≠ 0:= by exact neg_ne_zero.mpr ht
            rcases h6 with h6 | h6 | h6
            .
                -- Subcase 1: (a, b, c) = (1/s, s, -1)
                rcases h6 with ⟨h6, h7, h8⟩
                replace h6 : a = -t:= by linarith
                replace h7 : b = 1 / (-t):= by linarith
                replace h8 : c = -1:= by linarith
                set s:= 1 / (-t) with hs
                replace h6 : a = 1 / s:= by
                    rw [hs]
                    field_simp
                    linarith
                clear_value s
                subst a b c
                simp
                use s
                refine ⟨h2, ?_⟩
                simp
            .
                -- Subcase 2: (a, b, c) = (t, -1, 1/t)
                rcases h6 with ⟨h6, h7, h8⟩
                replace h6 : a = -t:= by linarith
                replace h8 : c = 1 / (-t):= by linarith
                replace h7 : b = -1:= by linarith
                set s:= -t with hs
                clear_value s
                subst a b c
                simp
                use s
                refine ⟨ht1, ?_⟩
                simp
            .
                -- Subcase 3: (a, b, c) = (-1, t, 1/t)
                rcases h6 with ⟨h6, h7, h8⟩
                replace h6 : a = -1:= by linarith
                replace h7 : b = -t:= by linarith
                replace h8 : c = 1 / (-t):= by linarith
                set s:= -t with hs
                clear_value s
                subst a b c
                simp
                use s
                refine ⟨ht1, ?_⟩
                simp
        .
            -- Case 2: abc > 0
            -- Apply lemma h6 directly to (a, b, c)
            specialize h6 a b c h1 h2 h3 h4 h5 g1
            rcases h6 with ⟨t, ht, h6⟩
            rcases h6 with h6 | h6 | h6
            all_goals
                rcases h6 with ⟨h6, h7, h8⟩
                subst a b c
                simp
                use t
                refine ⟨ht, ?_⟩
                simp
    .
        -- Prove the reverse direction: show that all claimed solutions satisfy the equations
        intro h
        simp at h
        rcases h with ⟨t, ht, h⟩
        rcases h with h | h | h | h | h | h
        all_goals
            rcases h with ⟨h1, h2, h3⟩
            subst a b c
            simp
            refine ⟨ht, ?_, ?_⟩
            ring_nf
            linarith
