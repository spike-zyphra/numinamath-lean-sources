import Mathlib

open Real Set
open scoped Real

/- If $\sin (\pi \cos x) = \cos (\pi \sin x),$ enter all possible values of $\sin 2x,$ separated by commas. -/
theorem calculus_23384 : {a : ℝ | ∃ x : ℝ, a = sin (2 * x) ∧ sin (π * cos x) = cos (π * sin x)} = {3 / 4, -3 / 4} := by
        ext a
        constructor
        .
            intro h
            simp at h
            rcases h with ⟨x, ha1, h⟩
            subst a
            simp
            -- 使用公式 sin a = cos (π / 2 - a)
            rw [show sin (π * cos x) = cos (π / 2 - π * cos x) by exact Eq.symm (cos_pi_div_two_sub (π * cos x))] at h
            -- 使用公式 cos x = cos y → ∃ (k : ℤ), y = 2 * ↑k * π + x ∨ y = 2 * ↑k * π - x
            replace h : ∃ (k : ℤ), π * sin x = 2 * ↑k * π + (π / 2 - π * cos x) ∨ π * sin x = 2 * ↑k * π - (π / 2 - π * cos x):= cos_eq_cos_iff.mp h
            rcases h with ⟨k, h⟩
            have hpos : π > 0:= pi_pos
            -- 分两种情况讨论
            rcases h with h | h
            .
                replace hpos : π ≠ 0:= by linarith
                replace h : π * (sin x + cos x - (2 * ↑k + 1 / 2)) = 0:= by linarith
                replace h : sin x + cos x - (2 * ↑k + 1 / 2) = 0:= eq_zero_of_ne_zero_of_mul_left_eq_zero hpos h
                replace h : sin x + cos x = (2 * ↑k + 1 / 2):= by linarith
                -- 证明 (sin x + cos x) ^ 2 ≤ 2
                have g1 : (sin x + cos x) ^ 2 ≤ 2:= by
                    ring_nf
                    have g2 : sin x ^ 2 + cos x ^ 2 = 1:= by exact sin_sq_add_cos_sq x
                    have g3 : sin (2 * x) = 2 * sin x * cos x:= by exact sin_two_mul x
                    rw [show sin x * cos x * 2 + sin x ^ 2 + cos x ^ 2 = sin (2 * x) + 1 by linarith]
                    have g4 : sin (2 * x) ≤ 1:= by exact sin_le_one (2 * x)
                    linarith
                -- 证明 k = 0
                have hkle1 : k < 1:= by
                    rify
                    by_contra!
                    replace h : sin x + cos x ≥ 5 / 2:= by linarith
                    nlinarith only [g1, h]
                have hkge0 : k > -1:= by
                    rify
                    by_contra!
                    replace h : sin x + cos x ≤ -3 / 2:= by linarith
                    nlinarith only [g1, h]
                have hkeq0 : k = 0:= by omega
                simp [hkeq0] at h
                clear hkge0 hkle1 hkeq0
                -- 证明 (sin x + cos x) ^ 2 = 1 + sin (2 * x)
                have h1 : (sin x + cos x) ^ 2 = 1 + sin (2 * x):= by
                    have _ : sin x ^ 2 + cos x ^ 2 = 1:= by exact sin_sq_add_cos_sq x
                    have _ : sin (2 * x) = 2 * sin x * cos x:= by exact sin_two_mul x
                    linarith
                ring_nf at h
                rw [h] at h1
                right
                linarith
            .
                replace hpos : π ≠ 0:= by linarith
                replace h : π * (sin x - cos x - (2 * ↑k - 1 / 2)) = 0:= by linarith
                replace h : sin x - cos x - (2 * ↑k - 1 / 2) = 0:= eq_zero_of_ne_zero_of_mul_left_eq_zero hpos h
                replace h : sin x - cos x = (2 * ↑k - 1 / 2):= by linarith
                -- 证明 (sin x - cos x) ^ 2 ≤ 2
                have g1 : (sin x - cos x) ^ 2 ≤ 2:= by
                    ring_nf
                    have g2 : sin x ^ 2 + cos x ^ 2 = 1:= by exact sin_sq_add_cos_sq x
                    have g3 : sin (2 * x) = 2 * sin x * cos x:= by exact sin_two_mul x
                    rw [show -(sin x * cos x * 2) + sin x ^ 2 + cos x ^ 2 = -sin (2 * x) + 1 by linarith]
                    have g4 : sin (2 * x) ≥ -1:= by exact neg_one_le_sin (2 * x)
                    linarith
                -- 证明 k = 0
                have hkle1 : k < 1:= by
                    rify
                    by_contra!
                    replace h : sin x - cos x ≥ 3 / 2:= by linarith
                    nlinarith only [g1, h]
                have hkge0 : k > -1:= by
                    rify
                    by_contra!
                    replace h : sin x - cos x ≤ -5 / 2:= by linarith
                    nlinarith only [g1, h]
                have hkeq0 : k = 0:= by omega
                simp [hkeq0] at h
                clear hkge0 hkle1 hkeq0
                -- 证明 (sin x - cos x) ^ 2 = 1 - sin (2 * x)
                have h1 : (sin x - cos x) ^ 2 = 1 - sin (2 * x):= by
                    have _ : sin x ^ 2 + cos x ^ 2 = 1:= by exact sin_sq_add_cos_sq x
                    have _ : sin (2 * x) = 2 * sin x * cos x:= by exact sin_two_mul x
                    linarith
                ring_nf at h
                rw [h] at h1
                left
                linarith
        .
            intro h
            simp at h
            have haeq : ∀ a : ℝ, a = arcsin (3 / 4) / 2 → sin a - cos a < 0:= by
                intro a ha
                have h3 : a < π / 4:= by
                    rw [ha]
                    suffices arcsin (3 / 4) < π / 2 by linarith
                    refine arcsin_lt_pi_div_two.mpr (by linarith)
                have h4 : a > 0:= by
                    rw [ha]
                    simp
                rw [show cos a = sin (π / 2 - a) by exact Eq.symm (sin_pi_div_two_sub a)]
                rw [Real.sin_sub_sin _ _]
                ring_nf
                have h5 : cos (π / 4) = √2 / 2:= by exact cos_pi_div_four
                rw [show π * (1 / 4) = π / 4 by ring]
                rw [h5]
                rw [show a + π * (-1 / 4) = a - π / 4 by ring]
                have _ : π > 0:= pi_pos
                replace h3 : a - π / 4 < 0:= by linarith
                replace h4 : a - π / 4 > -π:= by linarith
                have h6 : sin (a - π / 4) < 0:= by exact sin_neg_of_neg_of_neg_pi_lt h3 h4
                replace h6 : -sin (a - π / 4) > 0:= by linarith
                replace h6 : -sin (a - π / 4) * (√2 / 2) * 2 > 0:= by positivity
                linarith
            rcases h with h | h
            . -- 处理 sin(2x) = 3/4 的情况
                subst a
                simp
                -- 使用 arcsin(3/4)/2 作为解
                use (Real.arcsin (3 / 4) / 2)
                constructor
                . -- 证明 sin(2x) = 3/4
                    ring_nf
                    refine Eq.symm (sin_arcsin (by linarith) (by linarith))
                . -- 证明 sin(π * cos x) = cos(π*sin x)
                    -- 设 a = arcsin(3/4)/2
                    set a:= Real.arcsin (3 / 4) / 2 with ha
                    -- 证明 sin(2a) = 3/4
                    have h1 : sin (2 * a) = 3 / 4:= by
                        rw [ha]
                        ring_nf
                        refine (sin_arcsin (by linarith) (by linarith))

                    -- 使用三角恒等式 sin(x) = cos(π/2 - x)
                    rw [show sin (π * cos a) = cos (π / 2 - π * cos a) by exact Eq.symm (cos_pi_div_two_sub (π * cos a))]
                    -- 使用余弦相等的条件
                    apply cos_eq_cos_iff.2
                    use 0
                    right
                    simp
                    -- 转化为代数等式
                    suffices π * (sin a - cos a + (1 / 2)) = 0 by linarith
                    suffices sin a - cos a + (1 / 2) = 0 by rw [this] ; simp
                    have h2:= haeq a ha
                    clear_value a
                    -- 使用平方关系证明
                    replace h1 : (sin a - cos a) ^ 2 = 1 / 4:= by
                        ring_nf
                        have g1:= sin_sq_add_cos_sq a
                        have g2:= sin_two_mul a
                        linarith
                    -- 因式分解
                    replace h1 : (sin a - cos a + 1 / 2) * (sin a - cos a - 1 / 2) = 0:= by linarith
                    have h3 : sin a - cos a - 1 / 2 ≠ 0:= by
                        by_contra!
                        linarith
                    -- 得到最终等式
                    replace h1 : sin a - cos a + 1 / 2 = 0:= by exact eq_zero_of_ne_zero_of_mul_right_eq_zero h3 h1
                    linarith
            . -- 处理 sin(2x) = -3/4 的情况
                subst a
                simp
                -- 使用 arcsin(-3/4)/2 作为解
                use -(Real.arcsin (3 / 4) / 2)
                constructor
                . -- 证明 sin(2x) = -3/4
                    ring_nf
                    rw [show sin (-arcsin (3 / 4)) = -sin (arcsin (3 / 4)) by exact sin_neg (arcsin (3 / 4))]
                    suffices sin (arcsin (3 / 4)) = 3 / 4 by linarith
                    exact (sin_arcsin (by linarith) (by linarith))
                . -- 证明 sin(π* cos x) = cos(π*sin x)
                    -- 设 a = arcsin(-3/4)/2
                    set a:= -(Real.arcsin (3 / 4) / 2) with ha
                    clear_value a
                    -- 证明 sin(2a) = -3/4
                    have h1 : sin (2 * a) = -3 / 4:= by
                        rw [ha]
                        ring_nf
                        rw [show sin (-arcsin (3 / 4)) = -sin (arcsin (3 / 4)) by exact sin_neg (arcsin (3 / 4))]
                        suffices sin (arcsin (3 / 4)) = 3 / 4 by linarith
                        refine (sin_arcsin (by linarith) (by linarith))
                    -- 使用三角恒等式
                    rw [show sin (π * cos a) = cos (π / 2 - π * cos a) by exact Eq.symm (cos_pi_div_two_sub (π * cos a))]
                    apply cos_eq_cos_iff.2
                    use 0
                    left
                    simp
                    -- 转化为代数等式
                    suffices π * (sin a + cos a - (1 / 2)) = 0 by linarith
                    suffices sin a + cos a - (1 / 2) = 0 by rw [this] ; simp
                    have h2 : sin a + cos a > 0:= by
                        rw [ha]
                        rw [show sin (-(arcsin (3 / 4) / 2)) = -sin (arcsin (3 / 4) / 2) by exact sin_neg (arcsin (3 / 4) / 2)]
                        rw [show cos (-(arcsin (3 / 4) / 2)) = cos (arcsin (3 / 4) / 2) by exact cos_neg (arcsin (3 / 4) / 2)]
                        specialize haeq (arcsin (3 / 4) / 2) (by simp)
                        linarith
                    -- 使用平方关系证明
                    replace h1 : (sin a + cos a) ^ 2 = 1 / 4:= by
                        ring_nf
                        have g1:= sin_sq_add_cos_sq a
                        have g2:= sin_two_mul a
                        linarith
                    -- 因式分解
                    replace h1 : (sin a + cos a - 1 / 2) * (sin a + cos a + 1 / 2) = 0:= by linarith
                    have h3 : sin a + cos a + 1 / 2 ≠ 0:= by
                        by_contra!
                        linarith
                    -- 得到最终等式
                    replace h1 : sin a + cos a - 1 / 2 = 0:= by exact eq_zero_of_ne_zero_of_mul_right_eq_zero h3 h1
                    linarith
