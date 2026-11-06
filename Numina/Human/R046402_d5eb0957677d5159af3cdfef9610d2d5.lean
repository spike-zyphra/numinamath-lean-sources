import Mathlib

/- Let $a,$ $b,$ $c$ be real numbers such that
\[|ax^2 + bx + c| \le 1\]for all $0 \le x \le 1.$  Find the largest possible value of $|a| + |b| + |c|.$ -/
theorem algebra_22606 :
    IsGreatest {t : ℝ | ∃ a b c : ℝ, t = |a| + |b| + |c| ∧ (∀ x ∈ Set.Icc 0 1, |a * x ^ 2 + b * x + c| ≤ 1)} 17 := by
        -- 分两步证明：能取等 + 最大值
        constructor <;>
        simp [upperBounds]
        -- 能取等
        .
            use 8
            use -8
            use 1
            constructor
            .
                norm_num
            .
                intro x h1 h2
                rw [show 8 * x ^ 2 + -8 * x + 1 = 8 * (x - 1 / 2) ^ 2 - 1 by ring_nf]
                have g1 : 8 * (x - 1 / 2) ^ 2 - 1 ≥ -1:= by
                    have _ : 8 * (x - 1 / 2) ^ 2 ≥ 0:= by positivity
                    linarith
                have g2 : 8 * (x - 1 / 2) ^ 2 - 1 ≤ 1:= by
                    nlinarith only [h1, h2]
                exact abs_le.2 ⟨(by linarith), (by linarith)⟩
        -- 最大值
        .
            intro t a b c ht hx
            -- 将 x = 0, 1 / 2, 1代入条件
            have h1 := hx 0
            have h2 := hx (1 / 2)
            have h3 := hx 1
            -- 简化条件
            simp at h1 h2 h3
            ring_nf at h1 h2
            replace h2 := h2 (by linarith)
            let p:= c
            let q:= a * (1 / 4) + b * (1 / 2) + c
            let r:= a + b + c
            -- 引入新变量 p, q, r
            have hp : p = c:= by rfl
            have hq : q = a * (1 / 4) + b * (1 / 2) + c:= by rfl
            have hr : r = a + b + c:= by rfl
            rw [←hp] at h1
            rw [←hq] at h2
            rw [←hr] at h3
            -- 反解得到 a, b, c 关于 p, q, r的表达式
            have ha : a = 2 * p - 4 * q + 2 * r:= by
                rw [hp, hq, hr]
                linarith
            have hb : b = -3 * p + 4 * q - r:= by
                rw [hp, hq, hr]
                linarith
            have hc : c = p:= by linarith
            rw [ht, ha, hb, hc]
            clear_value p q r
            -- 证明 |2 * p - 4 * q + 2 * r| ≤ 8
            have h1 : |2 * p - 4 * q + 2 * r| ≤ 8:= by
                calc _ ≤ |2 * p - 4 * q| + |2 * r|:= by exact abs_add_le (2 * p - 4 * q) (2 * r)
                     _ ≤ |2 * p| + |4 * q| + |2 * r|:= by linarith only [abs_sub (2 * p) (4 * q)]
                     _ = 2 * |p| + 4 * |q| + 2 * |r|:= by
                        have g1 : |2 * p| = |2| * |p|:= by exact abs_mul 2 p
                        have g2 : |4 * q| = |4| * |q|:= by exact abs_mul 4 q
                        have g3 : |2 * r| = |2| * |r|:= by exact abs_mul 2 r
                        norm_num at g1 g2 g3
                        linarith
                     _ ≤ 8:= by linarith
            -- 证明 |-3 * p + 4 * q - r| ≤ 8
            have h2 : |-3 * p + 4 * q - r| ≤ 8:= by
                calc _ ≤ |-3 * p + 4 * q| + |r|:= by exact abs_sub (-3 * p + 4 * q) r
                     _ ≤ |-3 * p| + |4 * q| + |r|:= by linarith only [abs_add_le (-3 * p) (4 * q)]
                     _ = 3 * |p| + 4 * |q| + |r|:= by
                        have g1 : |-3 * p| = |-3| * |p|:= by exact abs_mul (-3) p
                        have g2 : |4 * q| = |4| * |q|:= by exact abs_mul 4 q
                        rw [g1, g2]
                        norm_num
                     _ ≤ 8:= by linarith
            linarith
