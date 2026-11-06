import Mathlib

/- For how many positive integer values of $k$ does $kx^2+10x+k=0$ have rational solutions? -/
theorem algebra_20817 :
    {k : ℤ | k > 0 ∧ ∃ x : ℚ, ↑k * x ^ 2 + 10 * x + ↑k = 0}.ncard = 3 := by
        -- 第一步：证明满足条件的k只能是3、4或5
        have h1 : {k : ℤ | k > 0 ∧ ∃ x : ℚ, ↑k * x ^ 2 + 10 * x + ↑k = 0} ⊆ {k : ℤ | k = 3 ∨ k = 4 ∨ k = 5}:= by
            simp
            intro k hk x hx
            have _ : ↑k ≠ 0:= by linarith
            -- 将方程变形为 k(x^2 + (10/k)x + 1) = 0
            replace hx : ↑k * (x ^ 2 + (10 / ↑k) * x + 1) = 0:= by
                ring_nf
                field_simp
                linarith
            -- 由于k≠0，可以消去k
            replace hx : x ^ 2 + 10 / ↑k * x + 1 = 0:= by
                calc _ = 1 * (x ^ 2 + 10 / ↑k * x + 1):= by linarith
                     _ = (1 / ↑k) * (↑k * (x ^ 2 + 10 / ↑k * x + 1)):= by field_simp
                     _ = (1 / ↑k) * 0:= by rw [hx]
                     _ = 0:= by ring
            -- 令t = 10/k，简化表达式
            let t : ℚ:= 10 / ↑k
            have ht : t = 10 / ↑k:= by rfl
            rw [←ht] at hx
            -- 使用配方法
            replace hx : (x + t / 2) ^ 2 = -1 + t ^ 2 / 4:= by linarith
            have h1 : t ^ 2 = 100 / (↑k ^ 2):= by
                rw [ht]
                ring
            rw [h1] at hx
            replace hx : (x + t / 2) ^ 2 = -1 + 25 / ↑k ^ 2:= by
                rw [hx]
                field_simp
                ring
            have h2 : (-1 : ℚ) + 25 / ↑k ^ 2 = (25 - ↑k ^ 2) / ↑k ^ 2:= by
                field_simp
                linarith
            rw [h2] at hx
            replace hx : 25 - ↑k ^ 2 = (↑k * (x + t / 2)) ^ 2:= by
                calc _ = ((25 : ℚ) - ↑k ^ 2) / ↑k ^ 2 * ↑k ^ 2:= by field_simp
                     _ = (x + t / 2) ^ 2 * ↑k ^ 2:= by rw [hx]
                     _ = (↑k * (x + t / 2)) ^ 2:= by ring
            -- 利用平方非负性
            have h3 : (↑k * (x + t / 2)) ^ 2 ≥ 0:= sq_nonneg ((↑k : ℚ) * (x + t / 2))
            replace h3 : (25 : ℚ) - ↑k ^ 2 ≥ 0:= by linarith
            replace h3 : ((5 : ℚ)  - ↑k) * ((5 : ℚ) + ↑k) ≥ 0:= by linarith
            have h5 : (↑k : ℚ) > 0:= by
                qify at hk
                linarith
            have h4 : (5 : ℚ) + ↑k > 0:= by linarith
            replace h3 : (5 : ℚ)  - ↑k ≥ 0:= by exact (mul_nonneg_iff_of_pos_right h4).mp h3
            -- 证明k≠1
            have hkne1 : k ≠ 1:= by
                by_contra H
                rw [H] at ht hx
                rw [ht] at hx
                simp at hx
                norm_num at hx
                have h : (x + 5) = (x + 5).num / (x + 5).den:= Eq.symm (Rat.num_div_den (x + 5))
                rw [h] at hx
                have h6 : ((↑(x + 5).num : ℚ) / ↑(x + 5).den) ^ 2 = (↑(x + 5).num) ^ 2 / (↑(x + 5).den) ^ 2:= by ring
                rw [h6] at hx
                replace hx : (24 : ℚ) * (↑(x + 5).den ^ 2) = ↑(x + 5).num ^ 2:= by
                    rw [hx]
                    field_simp
                replace hx : 24 * (x + 5).den ^ 2 = (x + 5).num ^ 2:= by
                    qify
                    exact hx
                have h7 : (↑(x + 5).den : ℤ) ^ 2 ∣ (x + 5).num ^ 2:= Dvd.intro_left 24 hx
                replace h7 : (↑(x + 5).den : ℤ) ∣ (x + 5).num:= by
                    have h8 : (↑(x + 5).den : ℤ) ^ 2 ∣  (↑(x + 5).num : ℤ) ^ 2 ↔ (↑(x + 5).den : ℤ) ∣ (↑(x + 5).num : ℤ):= Int.pow_dvd_pow_iff (by omega)
                    exact h8.1 h7
                replace h7 : ∃ a : ℤ, (x + 5).num = a * (↑(x + 5).den : ℤ):= exists_eq_mul_left_of_dvd h7
                rcases h7 with ⟨a, ha⟩
                rw [ha] at hx
                ring_nf at hx
                have h7 : ↑(5 + x).den ≠ 0:= by exact (5 + x).den_nz
                replace h7 : (↑(5 + x).den : ℤ) ≠ 0:= by omega
                replace h7 : (↑(5 + x).den : ℤ) ^ 2 ≠ 0:= by exact pow_ne_zero 2 h7
                replace hx : 24 = a ^ 2:= by exact (Int.mul_eq_mul_left_iff h7).mp hx
                have h8 : a ^ 2 = |a| ^ 2:= by exact Eq.symm (sq_abs a)
                rw [h8] at hx
                clear h7 h8
                have h7 : |a| ≥ 0:= by exact abs_nonneg a
                have ha1 : |a| < 5:= by
                    by_contra!
                    have h8 : 25 ≤ |a| ^ 2:= by nlinarith only [h7, this]
                    omega
                have ha2 : |a| > 4:= by
                    by_contra!
                    have h8 : 16 ≥ |a| ^ 2:= by nlinarith only [h7, this]
                    omega
                omega
            -- 证明k≠2
            have hkne2 : k ≠ 2:= by
                by_contra H
                rw [H] at ht hx
                rw [ht] at hx
                simp at hx
                norm_num at hx
                have h6 : 2 * (x + 5 / 2) = 2 * x + 5:= by ring_nf
                rw [h6] at hx
                clear h6
                have h : (2 * x + 5) = (2 * x + 5).num / (2 * x + 5).den:= Eq.symm (Rat.num_div_den (2 * x + 5))
                rw [h] at hx
                have h6 : ((↑(2 * x + 5).num : ℚ) / ↑(2 * x + 5).den) ^ 2 = (↑(2 * x + 5).num) ^ 2 / (↑(2 * x + 5).den) ^ 2:= by ring
                rw [h6] at hx
                replace hx : (21 : ℚ) * (↑(2 * x + 5).den ^ 2) = ↑(2 * x + 5).num ^ 2:= by
                    rw [hx]
                    field_simp
                replace hx : 21 * (2 * x + 5).den ^ 2 = (2 * x + 5).num ^ 2:= by
                    qify
                    exact hx
                have h7 : (↑(2 * x + 5).den : ℤ) ^ 2 ∣ (2 * x + 5).num ^ 2:= Dvd.intro_left 21 hx
                replace h7 : (↑(2 * x + 5).den : ℤ) ∣ (2 * x + 5).num:= by
                    have h8 : (↑(2 * x + 5).den : ℤ) ^ 2 ∣  (↑(2 * x + 5).num : ℤ) ^ 2 ↔ (↑(2 * x + 5).den : ℤ) ∣ (↑(2 * x + 5).num : ℤ):= Int.pow_dvd_pow_iff (by omega)
                    exact h8.1 h7
                replace h7 : ∃ a : ℤ, (2 * x + 5).num = a * (↑(2 * x + 5).den : ℤ):= exists_eq_mul_left_of_dvd h7
                rcases h7 with ⟨a, ha⟩
                rw [ha] at hx
                ring_nf at hx
                have h7 : ↑(5 + x * 2).den ≠ 0:= by exact (5 + x * 2).den_nz
                replace h7 : (↑(5 + x * 2).den : ℤ) ≠ 0:= by omega
                replace h7 : (↑(5 + x * 2).den : ℤ) ^ 2 ≠ 0:= by exact pow_ne_zero 2 h7
                replace hx : 21 = a ^ 2:= by exact (Int.mul_eq_mul_left_iff h7).mp hx
                have h8 : a ^ 2 = |a| ^ 2:= by exact Eq.symm (sq_abs a)
                rw [h8] at hx
                clear h7 h8
                have h7 : |a| ≥ 0:= by exact abs_nonneg a
                have ha1 : |a| < 5:= by
                    by_contra!
                    have h8 : 25 ≤ |a| ^ 2:= by nlinarith only [h7, this]
                    omega
                have ha2 : |a| > 4:= by
                    by_contra!
                    have h8 : 16 ≥ |a| ^ 2:= by nlinarith only [h7, this]
                    omega
                omega
            by_contra H
            simp at H
            rcases H with ⟨H1, H2, H3⟩
            replace h3 : 5 - k ≥ 0:= by
                qify
                linarith
            omega
        -- 第二步：证明k=3、4、5时确实都有解
        have h2 : {k : ℤ | k = 3 ∨ k = 4 ∨ k = 5} ⊆ {k : ℤ | k > 0 ∧ ∃ x : ℚ, ↑k * x ^ 2 + 10 * x + ↑k = 0}:= by
            simp
            constructor
            . -- k=3时，x=-1/3是解
                use (-1 / 3)
                norm_num
            .
                constructor
                . -- k=4时，x=-2是解
                    use -2
                    norm_num
                . -- k=5时，x=-1是解
                    use -1
                    norm_num
        -- 第三步：由两个子集的包含关系，得到集合相等
        have h3 : {k : ℤ | k > 0 ∧ ∃ x : ℚ, ↑k * x ^ 2 + 10 * x + ↑k = 0} = {k : ℤ | k = 3 ∨ k = 4 ∨ k = 5}:= Set.Subset.antisymm h1 h2
        -- 最后：计算集合{3,4,5}的基数为3
        clear h1 h2
        rw [h3]
        rw [show ({k : ℤ | k = 3 ∨ k = 4 ∨ k = 5} : Set ℤ) = ({3, 4, 5} : Set ℤ) by exact rfl]
        change Set.ncard ({3, 4, 5} : Set ℤ) = 3
        rw [show ({3, 4, 5} : Set ℤ) = ({3, 4, 5} : Finset ℤ) by simp]
        rw [Set.ncard_coe_Finset]
        rw [Finset.card_insert_of_not_mem]
        rw [Finset.card_insert_of_not_mem]
        simp
        .
            simp
        .
            simp
