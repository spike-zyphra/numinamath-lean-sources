import Mathlib

/- Three distinct integers $a,$ $b,$ and $c$ have the following properties:

$\bullet$ $abc = 17955$

$\bullet$ $a,$ $b,$ $c$ are three consecutive terms of an arithmetic sequence, in that order

$\bullet$ $3a + b$, $3b + c$, $3c + a$ are three consecutive terms of a geometric sequence, in that order
 -/

theorem algebra_18892 {a b c : ℤ} (h₀ : a * b * c = 17955) (h₁ : ∃ d : ℝ, b = a + d ∧ c = b + d)
    (h₂ : ∃ r : ℝ, 3 * b + c = (3 * a + b) * r ∧ 3 * c + a = (3 * b + c) * r) :
    a + b + c = -63 := by
        -- 从 h₁ 中提取公差 d 和两个等式
        rcases h₁ with ⟨d, h1, h2⟩
        -- 从 h₂ 中提取公比 r 和两个等式
        rcases h₂ with ⟨r, h3, h4⟩

        -- 证明：等比数列中间项的平方等于两端项的乘积
        have h6 : (3 * (↑b : ℝ) + (↑c : ℝ)) ^ 2 = (3 * (↑c : ℝ) + (↑a : ℝ)) * (3 * (↑a : ℝ) + (↑b : ℝ)) := by
            rw [h4]  -- 使用等比关系
            rw [h3]  -- 使用等比关系
            ring_nf  -- 代数化简

        -- 清理不再需要的假设
        clear h3 h4
        clear r

        -- 重写 a 和 c，用 b 和公差 d 表示
        replace h1 : ↑a = ↑b - d:= by linarith
        replace h2 : ↑c = ↑b + d:= by linarith

        -- 将 a 和 c 的表达式代入 h6 并化简
        rw [h1,h2] at h6
        ring_nf at h6

        -- 得到关于 d 的方程：d(12b + 7d) = 0
        have h7 : d * (12 * ↑b + 7 * d) = 0:= by linarith

        -- 证明 d ≠ 0（通过反证法）
        have h8 : d ≠ 0:= by
            by_contra!  -- 假设 d = 0
            simp [this] at h1 h2
            rw [h1,h2] at h₀
            rify at h₀
            -- 证明 b > 0
            have hpos : ↑b > 0:= by
                by_contra hb
                simp at hb
                rify at hb
                have hne : (↑b : ℝ) * (↑b : ℝ) * (↑b : ℝ) ≤ 0:= by
                    calc _ = (↑b : ℝ) ^ 2 * ↑b:= by ring_nf
                         _ ≤ (↑b : ℝ) ^ 2 * 0:= mul_le_mul_of_nonneg_left hb (sq_nonneg (b : ℝ))
                         _ = 0:= by ring_nf
                rw [h₀] at hne
                linarith
            rify at hpos
            -- 证明 b > 26（通过反证法）
            have h9 : (↑b : ℝ) > 26:= by
                by_contra hb
                simp at hb
                -- 如果 b ≤ 26，则 b³ ≤ 26³ = 17576
                have ha : (↑b : ℝ) * (↑b : ℝ) * (↑b : ℝ) ≤ 17576:= by
                    calc _ = (↑b : ℝ) ^ 2 * ↑b:= by ring_nf
                         _ ≤ (↑b : ℝ) ^ 2 * 26:= mul_le_mul_of_nonneg_left hb (sq_nonneg (b : ℝ))
                         _ = (26 * (↑b : ℝ)) * (↑b : ℝ):= by ring_nf
                         _ ≤ (26 * (↑b : ℝ)) * 26:= mul_le_mul_of_nonneg_left (by linarith) (by linarith)
                         _ = (26 * 26) * (↑b : ℝ):= by ring_nf
                         _ ≤ (26 * 26) * 26:= mul_le_mul_of_nonneg_left (by linarith) (by linarith)
                         _ = 17576:= by ring_nf
                rw [h₀] at ha
                linarith
            -- 证明 b < 27（通过反证法）
            have h10 : (↑b : ℝ) < 27:= by
                by_contra hb
                simp at hb
                -- 如果 b ≥ 27，则 b³ ≥ 27³ = 19683
                have ha : (↑b : ℝ) * (↑b : ℝ) * (↑b : ℝ) ≥ 19683:= by
                    calc _ = (↑b : ℝ) ^ 2 * ↑b:= by ring_nf
                         _ ≥ (↑b : ℝ) ^ 2 * 27:= mul_le_mul_of_nonneg_left hb (sq_nonneg (b : ℝ))
                         _ = (27 * (↑b : ℝ)) * (↑b : ℝ):= by ring_nf
                         _ ≥ (27 * (↑b : ℝ)) * 27:= mul_le_mul_of_nonneg_left (by linarith) (by linarith)
                         _ = (27 * 27) * (↑b : ℝ):= by ring_nf
                         _ ≥ (27 * 27) * 27:= mul_le_mul_of_nonneg_left (by linarith) (by linarith)
                         _ = 19683:= by ring_nf
                rw [h₀] at ha
                linarith
            -- 将实数不等式转换为整数不等式
            replace h9 : b > 26:= by
                rify
                linarith
            replace h10 : b < 27:= by
                rify
                linarith
            -- 得到矛盾：26 < b < 27，但 b 是整数
            replace h10 : b ≤ 26:= by omega
            omega
        -- 由 d ≠ 0 得到 12b + 7d = 0
        have h9 : (12 * ↑b + 7 * d) = 0:= by exact eq_zero_of_ne_zero_of_mul_left_eq_zero h8 h7
        clear h7 h8
        replace h9 : d = (-12 / 7) * (↑b : ℝ):= by linarith
        replace h1 : (↑a : ℝ) = (19 / 7) * (↑b : ℝ):= by linarith
        replace h2 : (↑c : ℝ) = (-5 / 7) * (↑b : ℝ):= by linarith
        rify at h₀
        rw [h1,h2] at h₀
        -- 得到 b³ = (-21)³
        have h10 : b ^ 3 = (-21) ^ 3:= by
            rify
            linarith
        -- 证明 b = -21
        have h11 : (↑b : ℝ) = -21:= by
            have h12 : (↑b : ℝ) ^ 3 = (-21 : ℝ) ^ 3 ↔ (↑b : ℝ) = (-21 : ℝ) ∨ (↑b : ℝ) = - (-21 : ℝ) ∧ Even 3:= pow_eq_pow_iff_of_ne_zero (show 3 ≠ 0 by omega)
            rify at h10
            apply h12.1 at h10
            rcases h10 with h10 | h10
            .
                exact h10
            .
                by_contra!
                replace h10 := h10.2
                trivial
        -- 最终求解得到 a、b、c 的值
        rw [h11] at h1 h2
        replace h11 : b = -21:= by
            rify
            linarith
        replace h1 : a = -57:= by
            rify
            linarith
        replace h2 : c = 15:= by
            rify
            linarith
        -- 验证 a + b + c = -63
        omega
