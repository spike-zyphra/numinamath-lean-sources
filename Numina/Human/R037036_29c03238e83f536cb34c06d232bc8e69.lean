import Mathlib

/- Given a right triangle whose side lengths are all integer multiples of 8, how many units are in the smallest possible perimeter of such a triangle? -/
theorem algebra_21902:
    IsLeast {s : ℕ | ∃ a b c : ℕ , s = a + b + c ∧ a > 0 ∧ b > 0 ∧ c > 0 ∧ a ^ 2 + b ^ 2 = c ^ 2 ∧ ∃ m n p : ℕ , a = 8 * m ∧ b = 8 * n ∧ c = 8 * p} 96 := by
        constructor <;>
        simp [lowerBounds]
        .   -- 第一部分：构造一个周长为96的例子
            use 24  -- a = 24
            use 32  -- b = 32
            use 40  -- c = 40
            simp
            constructor
            .   -- 证明 24 = 8 * 3
                use 3
            .
                constructor
                .   -- 证明 32 = 8 * 4
                    use 4
                .   -- 证明 40 = 8 * 5
                    use 5
        .   -- 第二部分：证明不存在小于96的解
            intro s a b c hs h1 h2 h3 hr m ha n hb p hc
            rw [ha, hb, hc] at hs hr  -- 将 a,b,c 用 8m,8n,8p 替换
            rw [ha] at h1
            rw [hb] at h2
            rw [hc] at h3
            replace h1 : 0 < m := by omega  -- 证明 m 是正数
            replace h2 : 0 < n := by omega  -- 证明 n 是正数
            replace h3 : 0 < p := by omega  -- 证明 p 是正数
            let t := m + n + p  -- 引入新变量 t 表示 m+n+p
            have ht : t = m + n + p := by rfl
            replace hs : s = 8 * t := by omega  -- 证明周长 s = 8(m+n+p)
            rw [hs]
            clear a b c ha hb hc hs
            have h4 : (8 * m) ^ 2 = 64 * m ^ 2 := by ring  -- 化简平方项
            have h5 : (8 * n) ^ 2 = 64 * n ^ 2 := by ring
            have h6 : (8 * p) ^ 2 = 64 * p ^ 2 := by ring
            rw [h4, h5, h6] at hr
            clear h4 h5 h6
            replace hr : 64 * (m ^ 2 + n ^ 2) = 64 * p ^ 2 := by omega
            replace hr : m ^ 2 + n ^ 2 = p ^ 2:= by omega  -- 得到简化的勾股定理
            suffices H : t ≥ 12 by omega  -- 如果能证明 m+n+p ≥ 12，则原命题得证
            have hmge3 : m ≥ 3 := by  -- 证明 m ≥ 3
                by_contra!  -- 反证法
                have hm : m ^ 2 > 0 := Nat.pos_pow_of_pos 2 h1
                have hnp1 : p ^ 2 > n ^ 2 := by omega
                have hnp2 : p > n := lt_of_pow_lt_pow_left' 2 hnp1
                zify at hr
                replace hr : ((↑p : ℤ) - ↑n) * (↑p + ↑n) = ↑m ^ 2 := by linarith
                have hmneq1 : m ≠ 1 := by  -- 证明 m ≠ 1
                    by_contra!
                    zify at this
                    rw [this] at hr
                    simp at hr
                    zify at hnp2
                    replace hnp2 : (↑p : ℤ) - ↑n > 0 := by linarith
                    have h7 : (↑p : ℤ) - ↑n ≤ 1 := by
                        by_contra H
                        simp at H
                        replace H : (↑p : ℤ) - ↑n ≥ 2 := by linarith
                        have h8 : (↑p : ℤ) + ↑n ≥ 1 := by linarith
                        have h9 : ((↑p : ℤ) - ↑n) * (↑p + ↑n) ≥ 2:= by nlinarith only [H, h8]
                        linarith
                    replace h7 : (↑p : ℤ) - ↑n = 1 := by linarith
                    have h8 : (↑p : ℤ) + ↑n = 1:= by
                        rw [h7] at hr
                        simp at hr
                        exact hr
                    linarith
                have hmneq2 : m ≠ 2 := by  -- 证明 m ≠ 2
                    by_contra!
                    zify at this
                    rw [this] at hr
                    simp at hr
                    have h7 : (↑p : ℤ) - ↑n ≤ 1 := by
                        by_contra H
                        simp at H
                        replace H : (↑p : ℤ) - ↑n ≥ 2 := by linarith
                        have h8 : (↑p : ℤ) + ↑n ≥ 3 := by linarith
                        have h9 : ((↑p : ℤ) - ↑n) * (↑p + ↑n) ≥ 6:= by nlinarith only [H, h8]
                        linarith
                    replace h7 : (↑p : ℤ) - ↑n = 1 := by linarith
                    have h8 : (↑p : ℤ) + ↑n = 4:= by
                        rw [h7] at hr
                        simp at hr
                        exact hr
                    have h9 : 2 * (↑p : ℤ) = 5 := by linarith
                    have h10 : 2 ∣ 2 * (↑p : ℤ):= Int.dvd_mul_right 2 (↑p : ℤ)
                    rw [h9] at h10
                    trivial
                omega
            have hnge3 : n ≥ 3 := by  -- 用类似方法证明 n ≥ 3
                by_contra!
                have hn : n ^ 2 > 0 := Nat.pos_pow_of_pos 2 h2
                have hnp1 : p ^ 2 > m ^ 2 := by omega
                have hnp2 : p > m := lt_of_pow_lt_pow_left' 2 hnp1
                zify at hr
                replace hr : ((↑p : ℤ) - ↑m) * (↑p + ↑m) = ↑n ^ 2 := by linarith
                have hnneq1 : n ≠ 1 := by
                    by_contra!
                    zify at this
                    rw [this] at hr
                    simp at hr
                    zify at hnp2
                    replace hnp2 : (↑p : ℤ) - ↑m > 0 := by linarith
                    have h7 : (↑p : ℤ) - ↑m ≤ 1 := by
                        by_contra H
                        simp at H
                        replace H : (↑p : ℤ) - ↑m ≥ 2 := by linarith
                        have h8 : (↑p : ℤ) + ↑m ≥ 3 := by linarith
                        have h9 : ((↑p : ℤ) - ↑m) * (↑p + ↑m) ≥ 6:= by nlinarith only [H, h8]
                        linarith
                    replace h7 : (↑p : ℤ) - ↑m = 1 := by linarith
                    have h8 : (↑p : ℤ) + ↑m = 1:= by
                        rw [h7] at hr
                        simp at hr
                        exact hr
                    linarith
                have hnneq2 : n ≠ 2 := by
                    by_contra!
                    zify at this
                    rw [this] at hr
                    simp at hr
                    have h7 : (↑p : ℤ) - ↑m ≤ 1 := by
                        by_contra H
                        simp at H
                        replace H : (↑p : ℤ) - ↑m ≥ 2 := by linarith
                        have h8 : (↑p : ℤ) + ↑m ≥ 3 := by linarith
                        have h9 : ((↑p : ℤ) - ↑m) * (↑p + ↑m) ≥ 6:= by nlinarith only [H, h8]
                        linarith
                    replace h7 : (↑p : ℤ) - ↑m = 1 := by linarith
                    have h8 : (↑p : ℤ) + ↑m = 4:= by
                        rw [h7] at hr
                        simp at hr
                        exact hr
                    linarith
                omega
            have hb : m ≥ 4 ∨ n ≥ 4 := by  -- 证明 m ≥ 4 或 n ≥ 4
                by_contra!
                have hmge3 : m = 3 := by omega
                have hnge3 : n = 3 := by omega
                rw [hmge3, hnge3] at hr
                zify at hr
                ring_nf at hr
                have h4 : (↑p : ℤ) > 3 := by
                    by_contra!
                    have _ : (↑p : ℤ) ^ 2 ≤ 9 := by nlinarith only [this]
                    linarith
                have h5 : (↑p : ℤ) < 5 := by
                    by_contra!
                    have _ : (↑p : ℤ) ^ 2 ≥ 25 := by nlinarith only [this]
                    linarith
                have h6 : (↑p : ℤ) = 4 := by linarith
                rw [h6] at hr
                ring_nf at hr
                linarith
            rw [ht]
            clear s t ht
            rcases hb with hb | hb
            .   -- 处理 m ≥ 4 的情况
                clear hmge3
                replace hb1 : m ^ 2 ≥ 16 := by nlinarith only [hb]
                replace hnge31 : n ^ 2 ≥ 9 := by nlinarith only [hnge3]
                replace hr : p ^ 2 ≥ 25 := by omega
                replace hr : p ≥ 5 := by
                    by_contra!
                    replace this : p ≤ 4 := by omega
                    replace this : p ^ 2 ≤ 16 := by nlinarith only [this]
                    omega
                omega
            .   -- 处理 n ≥ 4 的情况
                replace hb1 : n ^ 2 ≥ 16 := by nlinarith only [hb]
                replace hmge31 : m ^ 2 ≥ 9 := by nlinarith only [hmge3]
                replace hr : p ^ 2 ≥ 25 := by omega
                replace hr : p ≥ 5 := by
                    by_contra!
                    replace this : p ≤ 4 := by omega
                    replace this : p ^ 2 ≤ 16 := by nlinarith only [this]
                    omega
                omega
