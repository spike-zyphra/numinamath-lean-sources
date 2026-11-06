import Mathlib
/- 7. A1 (USA) ${ }^{\mathrm{IMO} 2}$ Let $a, b, c$ be positive real numbers with product 1. Prove that  $$ \left(a-1+\frac{1}{b}\right)\left(b-1+\frac{1}{c}\right)\left(c-1+\frac{1}{a}\right) \leq 1 . $$ -/

theorem algebra_25026 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) :
    (a - 1 + 1 / b) * (b - 1 + 1 / c) * (c - 1 + 1 / a) ≤ 1 := by

    -- First key inequality: (a - 1 + 1/b)(b - 1 + 1/c) ≤ a/c
    have h1 : (a - 1 + 1 / b) * (b - 1 + 1 / c) ≤ a / c:= by
        have h1 : (a - 1 + 1 / b) * (b - 1 + 1 / c) = a / c - b - 1 / b + 2:= by
            replace habc : a = 1 / (b * c):= by
                field_simp
                linarith
            rw [habc]
            field_simp
            linarith
        have h2 : b + 1 / b - 2 ≥ 0:= by
            rw [show b + 1 / b - 2 = (b - 1) ^ 2 / b by field_simp ; linarith]
            positivity
        linarith
    have h2 : (b - 1 + 1 / c) * (c - 1 + 1 / a) ≤ b / a:= by
        have h2 : (b - 1 + 1 / c) * (c - 1 + 1 / a) = b / a - c - 1 / c + 2:= by
            replace habc : b = 1 / (c * a):= by
                field_simp
                linarith
            rw [habc]
            field_simp
            linarith
        have h3 : c + 1 / c - 2 ≥ 0:= by
            rw [show c + 1 / c - 2 = (c - 1) ^ 2 / c by field_simp ; linarith]
            positivity
        linarith
    have h3 : (c - 1 + 1 / a) * (a - 1 + 1 / b) ≤ c / b:= by
        have h3 : (c - 1 + 1 / a) * (a - 1 + 1 / b) = c / b - a - 1 / a + 2:= by
            replace habc : c = 1 / (a * b):= by
                field_simp
                linarith
            rw [habc]
            field_simp
            linarith
        have h4 : a + 1 / a - 2 ≥ 0:= by
            rw [show a + 1 / a - 2 = (a - 1) ^ 2 / a by field_simp ; linarith]
            positivity
        linarith
    by_cases h : (a - 1 + 1 / b) * (b - 1 + 1 / c) * (c - 1 + 1 / a) ≥ 0
    .
        -- Case 1: Product is non-negative
        -- Strategy: Square both sides and prove (product)² ≤ 1
        suffices ((a - 1 + 1 / b) * (b - 1 + 1 / c) * (c - 1 + 1 / a)) ^ 2 ≤ 1 by exact (sq_le_one_iff h).mp this

        -- Prove that all three factors are non-negative
        have hpos : a - 1 + 1 / b ≥ 0 ∧ b - 1 + 1 / c ≥ 0 ∧ c - 1 + 1 / a ≥ 0:= by
            by_contra H
            simp at H
            by_cases g1 : a - 1 + b⁻¹ < 0
            .
                rw [show b⁻¹ = 1 / b by field_simp] at g1
                replace h : (b - 1 + 1 / c) * (c - 1 + 1 / a) ≤ 0:= by
                    by_contra H1
                    simp at H1
                    rw [show c⁻¹ = 1 / c by field_simp] at H1
                    rw [show a⁻¹ = 1 / a by field_simp] at H1
                    replace g1 : -(a - 1 + 1 / b) > 0:= by linarith only [g1]
                    replace H1 : (-(a - 1 + 1 / b)) * ((b - 1 + 1 / c) * (c - 1 + 1 / a)) > 0:= by positivity
                    linarith
                by_cases g2 : b - 1 + 1 / c ≤ 0
                .
                    have g3 : b < 1:= by
                        by_contra H2
                        simp at H2
                        have g4 : 1 / c > 0:= by positivity
                        linarith
                    replace g3 : 1 / b > 1:= by exact one_lt_one_div hb g3
                    linarith
                .
                    simp at g2
                    rw [show c⁻¹ = 1 / c by field_simp] at g2
                    replace h : c - 1 + 1 / a ≤ 0:= by exact nonpos_of_mul_nonpos_right h g2
                    have g3 : a < 1:= by
                        by_contra H2
                        simp at H2
                        have g4 : 1 / b > 0:= by positivity
                        linarith
                    replace g3 : 1 / a > 1:= by exact one_lt_one_div ha g3
                    linarith
            .
                simp at g1
                replace H:= H g1
                by_cases g2 : b - 1 + c⁻¹ ≥ 0
                .
                    replace H:= H g2
                    rw [show c⁻¹ = 1 / c by field_simp] at g2
                    rw [show a⁻¹ = 1 / a by field_simp] at H
                    rw [show b⁻¹ = 1 / b by field_simp] at g1
                    by_cases g3 : a - 1 + 1 / b = 0
                    .
                        have g4 : a < 1:= by
                            by_contra H2
                            simp at H2
                            have g5 : 1 / b > 0:= by positivity
                            linarith
                        replace g4 : 1 / a > 1:= by exact one_lt_one_div ha g4
                        linarith
                    .
                        replace g1 : a - 1 + 1 / b > 0:= by positivity
                        clear g3
                        by_cases g3 : b - 1 + 1 / c = 0
                        .
                            have g4 : c ≥ 1:= by
                                by_contra H2
                                simp at H2
                                replace H2 : 1 / c > 1:= by exact one_lt_one_div hc H2
                                linarith
                            have g5 : 1 / a > 0:= by positivity
                            linarith
                        .
                            replace g2 : b - 1 + 1 / c > 0:= by positivity
                            clear g3
                            replace H : -(c - 1 + 1 / a) > 0:= by linarith only [H]
                            have g3 : (-(c - 1 + 1 / a)) * ((a - 1 + 1 / b) * (b - 1 + 1 / c)) > 0:= by positivity
                            linarith
                .
                    simp at g2
                    rw [show c⁻¹ = 1 / c by field_simp] at g2
                    rw [show b⁻¹ = 1 / b by field_simp] at g1
                    clear H
                    by_cases g3 : a - 1 + 1 / b = 0
                    .
                        have g4 : b ≥ 1:= by
                            by_contra H2
                            simp at H2
                            have g5 : 1 / b > 1:= by exact one_lt_one_div hb H2
                            linarith
                        have g5 : 1 / c > 0:= by positivity
                        linarith
                    .
                        replace g1 : a - 1 + 1 / b > 0:= by positivity
                        clear g3
                        have g3 : c - 1 + 1 / a ≤ 0:= by
                            by_contra H2
                            simp at H2
                            rw [show a⁻¹ = 1 / a by field_simp] at H2
                            replace g2 : -(b - 1 + 1 / c) > 0:= by linarith only [g2]
                            have g3 : (-(b - 1 + 1 / c)) * ((a - 1 + 1 / b) * (c - 1 + 1 / a)) > 0:= by positivity
                            linarith
                        have g4 : c < 1:= by
                            by_contra H2
                            simp at H2
                            have g5 : 1 / a > 0:= by positivity
                            linarith
                        replace g4 : 1 / c > 1:= by exact one_lt_one_div hc g4
                        linarith
        rcases hpos with ⟨ga, gb, gc⟩
        have h4 : ((a - 1 + 1 / b) * (b - 1 + 1 / c)) * ((b - 1 + 1 / c) * (c - 1 + 1 / a)) ≤ (a / c) * (b / a):= by refine mul_le_mul_of_nonneg h1 h2 (by positivity) (by positivity)
        replace h4 : ((a - 1 + 1 / b) * (b - 1 + 1 / c)) * ((b - 1 + 1 / c) * (c - 1 + 1 / a)) * ((c - 1 + 1 / a) * (a - 1 + 1 / b)) ≤ (a / c) * (b / a) * (c / b):= by refine mul_le_mul_of_nonneg h4 h3 (by positivity) (by positivity)
        rw [show ((a - 1 + 1 / b) * (b - 1 + 1 / c)) * ((b - 1 + 1 / c) * (c - 1 + 1 / a)) * ((c - 1 + 1 / a) * (a - 1 + 1 / b)) = ((a - 1 + 1 / b) * (b - 1 + 1 / c) * (c - 1 + 1 / a)) ^ 2 by ring] at h4
        rw [show (a / c) * (b / a) * (c / b) = 1 by field_simp ; linarith] at h4
        exact h4
    .
        -- Case 2: Product is negative
        -- Direct proof using the fact that negative ≤ 1
        simp at h
        rw [show a⁻¹ = 1 / a by field_simp] at h
        rw [show b⁻¹ = 1 / b by field_simp] at h
        rw [show c⁻¹ = 1 / c by field_simp] at h
        linarith only [h]
