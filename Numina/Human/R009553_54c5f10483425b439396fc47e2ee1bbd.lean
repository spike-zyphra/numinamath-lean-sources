import Mathlib
open Real

/- Suppose the function $\psi$ satisfies $\psi(1) = \sqrt{2 + \sqrt{2 + \sqrt{2}}}$ and
\[\psi(3x) + 3 \psi(x) = \psi^3(x)\]for all real $x.$  Determine $\prod_{n = 1}^{100} \psi(3^n).$ -/
/- Suppose the function $\psi$ satisfies $\psi(1) = \sqrt{2 + \sqrt{2 + \sqrt{2}}}$ and
\[\psi(3x) + 3 \psi(x) = \psi^3(x)\]for all real $x.$  Determine $\prod_{n = 1}^{100} \psi(3^n).$ -/
theorem calculus_23276 {ψ : ℝ → ℝ}
    (hψ1 : ψ 1 = √(2 + √(2 + √2)))
    (hψ : ∀ x, ψ (3 * x) + 3 * ψ x = (ψ x) ^ 3) :
    ∏ n ∈ Finset.Icc 1 100, ψ (3 ^ n) = 4096 * sqrt 2 := by
        have := pi_pos
        -- 核心引理: 对于任意自然数k，前4k项的乘积等于(√2)^k
        have h : ∀ k : ℕ, (∏ n ∈ Finset.Icc 1 (4 * k), ψ (3 ^ n) = (√2) ^ k):= by
            intro n; induction n with
            | zero => norm_num
            | succ k ih =>
            -- 定义辅助函数f(n) = ψ(3ⁿ)
            set f : ℕ → ℝ:= fun n => ψ (3 ^ n) with hf
            -- 使用Finset.prod_Icc_succ_top拆分乘积
            simp[mul_add, Finset.prod_Icc_succ_top]
            rw [ih]
            -- 使用三角函数恒等式
            have h1 : cos (π / 4) = √2 / 2:= cos_pi_div_four
            replace h1 : √2 = 2 * cos (π / 4):= by linarith
            rw [h1] at hψ1
            -- 使用余弦平方公式
            have h2 : (cos (π / 8)) ^ 2 = 1 / 2 + cos (2 * (π / 8)) / 2 := Real.cos_sq (π / 8)
            rw [show 2 * (π / 8) = π / 4 by linarith] at h2
            replace h2 : 2 + 2 * cos (π / 4) = (2 * cos (π / 8)) ^ 2:= by linarith
            have h3 : π / 8 ∈ Set.Icc (-(π / 2)) (π / 2):= by
                simp; constructor
                all_goals linarith
            have h4 : cos (π / 8) ≥ 0:= cos_nonneg_of_mem_Icc h3
            replace h4 : 2 * cos (π / 8) ≥ 0:= by linarith
            have h5 : √((2 * cos (π / 8)) ^ 2) = 2 * cos (π / 8):= sqrt_sq h4
            rw [h2, h5] at hψ1
            have h6 : (cos (π / 16)) ^ 2 = 1 / 2 + cos (2 * (π / 16)) / 2:= Real.cos_sq (π / 16)
            rw [show 2 * (π / 16) = π / 8 by linarith] at h6
            replace h6 : 2 + 2 * cos (π / 8) = (2 * cos (π / 16)) ^ 2:= by linarith
            have h7 : π / 16 ∈ Set.Icc (-(π / 2)) (π / 2):= by
              simp; constructor
              all_goals linarith
            have h8 : cos (π / 16) ≥ 0:= cos_nonneg_of_mem_Icc h7
            replace h8 : 2 * cos (π / 16) ≥ 0:= by linarith
            have h9 : √((2 * cos (π / 16)) ^ 2) = 2 * cos (π / 16):= sqrt_sq h8
            rw [h6, h9] at hψ1; clear h1 h2 h3 h4 h5 h6 h7 h8 h9
            -- 证明关键等式: ψ(3ⁿ) = 2cos(3ⁿ * π/16)
            have g : ∀ n : ℕ, ψ ((3 : ℝ) ^ n) = 2 * cos (3 ^ n * (π / 16)):= by
                intro n; induction n with
                | zero =>
                norm_num; norm_num at hψ1
                exact hψ1
                | succ t ih1 =>
                specialize hψ (3 ^ t)
                rw [ih1] at hψ
                -- 使用三倍角公式
                have g1 : cos (3 * (3 ^ t *(π / 16))) = 4 * cos (3 ^ t * (π / 16)) ^ 3 - 3 * cos (3 ^ t * (π / 16)):= cos_three_mul (3 ^ t * (π / 16))
                rw [← pow_succ'] at hψ
                rw [show 3 * (3 ^ t * (π / 16)) = 3 ^ (t + 1) * (π / 16) by ring] at g1
                linarith
            dsimp [f]; simp [g]; ring_nf
            set t := π * 3 ^ (k * 4) / 16 with ht
            rw [show π * (3 : ℝ) ^ (k * 4) * (3 / 16) = 3 * t by rw [ht]; ring]
            rw [show π * (3 : ℝ) ^ (k * 4) * (9 / 16) = 9 * t by rw [ht]; ring]
            rw [show π * (3 : ℝ) ^ (k * 4) * (27 / 16) = 27 * t by rw [ht]; ring]
            rw [show π * (3 : ℝ) ^ (k * 4) * (81 / 16) = 81 * t by rw [ht]; ring]
            -- 证明3ⁿ-1被2整除
            have h1 : ∀ n : ℕ, 2 ∣ (3 : ℤ) ^ n - 1:= by
                intro s; induction s with
                | zero => norm_num
                | succ s ih2 =>
                rw [pow_succ]
                rw [show (3 : ℤ) ^ s * 3 - 1 = 3 * (3 ^ s - 1) + 2 by omega]
                have h1 : (2 : ℤ) ∣ 2:= by rfl
                have h2 : (2 : ℤ) ∣ 3 * (3 ^ s - 1):= Dvd.dvd.mul_left ih2 3
                exact (Int.dvd_add_right h2).mpr h1
            have hk : ∃ k_1 : ℤ, π + ↑k_1 * (2 * π) = π * 3 ^ (k * 4):= by
                specialize h1 (k * 4); rcases h1 with ⟨k_2, hk2⟩
                use k_2; rify at hk2
                replace hk2 : (3 : ℝ) ^ (k * 4) = 2 * ↑k_2 + 1:= by linarith
                rw [hk2]; ring
            have gk : ∃ (n : ℤ), ↑n * Real.pi = π * 3 ^ (k * 4):= by
                use (3 : ℤ) ^ (k * 4); norm_cast; linarith
            -- 使用三角函数周期性
            have hk1 : cos (π * 3 ^ (k * 4)) = -1:= cos_eq_neg_one_iff.mpr hk
            have hk2 : sin (π * 3 ^ (k * 4)) = 0:= sin_eq_zero_iff.mpr gk
            have g1 : ∀ (s : ℝ), cos (s + 16 * t) = - cos s:= by
                intro s
                calc _ = cos (s + π * 3 ^ (k * 4)):= by rw [show 16 * t = π * 3 ^ (k * 4) by linarith]
                     _ = cos s * cos (π * 3 ^ (k * 4)) - sin s * sin (π * 3 ^ (k * 4)):= cos_add s (π * 3 ^ (k * 4))
                     _ = cos s * (-1) - sin s * 0:= by rw [hk1, hk2]
                     _ = - cos s:= by simp
            clear ih hf g
            have g2 := g1 t; have g3 := g1 (17 * t)
            have g4 := g1 (33 * t); have g5 := g1 (49 * t)
            have g6 := g1 (65 * t); specialize g1 (11 * t)
            have hkk : ∃ (k_2 : ℤ), (π / 2) * 3 ^ (k * 4) = (2 * ↑k_2 + 1) * Real.pi / 2:= by
                rcases hk with ⟨k_1, hk⟩; use k_1; linarith
            have gkk : ∃ (k_1 : ℤ), Real.pi / 2 + ↑k_1 * (2 * Real.pi) = (π / 2) * 3 ^ (k * 4):= by
                specialize h1 (k * 2); rcases h1 with ⟨k_1, h1⟩
                have h2 : 3 ^ (k * 2) + 1 = 2 * k_1 + 2:= by linarith
                have h3 : 3 ^ (k * 4) - 1 = 4 * (k_1 + 1) * k_1:= by
                    calc _ = (3 : ℤ) ^ (k * 2 + k * 2) - 1:= by rw [show k * 4 = k * 2 + k * 2 by omega]
                         _ = (3 : ℤ) ^ (k * 2) * 3 ^ (k * 2) - 1:= by ring
                         _ = ((3 : ℤ) ^ (k * 2) - 1) * ((3 : ℤ) ^ (k * 2) + 1):= by ring
                         _ = (2 * k_1) * (2 * k_1 + 2):= by rw [h1, h2]
                         _ = _:= by ring
                use (k_1 + 1) * k_1
                rify at h3; ring_nf
                rw [show (↑(k_1 + k_1 ^ 2) : ℝ) = ↑k_1 + ↑k_1 ^ 2 by norm_cast]
                replace h3 : (3 ^ (k * 4) : ℝ) = 4 * (↑k_1 + 1) * ↑k_1 + 1:= by linarith
                rw [show π * 3 ^ (k * 4) = π * (3 ^ (k * 4)) by ring]
                rw [h3]; ring
            have hk3 : cos ((π / 2) * 3 ^ (k * 4)) = 0:= Real.cos_eq_zero_iff.mpr hkk
            have hk4 : sin ((π / 2) * 3 ^ (k * 4)) = 1:= Real.sin_eq_one_iff.mpr gkk
            have h2 : ∀ (s : ℝ), cos (s + 8 * t) = - sin s:= by
                intro s
                calc _ = cos (s + (π / 2) * 3 ^ (k * 4)):= by rw [show 8 * t = (π / 2) * 3 ^ (k * 4) by linarith]
                     _ = cos s * cos ((π / 2) * 3 ^ (k * 4)) - sin s * sin ((π / 2) * 3 ^ (k * 4)):= cos_add s ((π / 2) * 3 ^ (k * 4))
                     _ = cos s * 0 - sin s * 1:= by rw [hk3, hk4]
                     _ = -sin s:= by simp
            norm_num [← add_mul] at g1 g3 g4 g5 g6
            rw [show t + 16 * t = 17 * t by linarith] at g2; rw [g1]
            have g7 : cos (81 * t) = -cos t:= by linarith
            rw [g7]; clear g1 g2 g3 g4 g5 g6 g7; simp
            have g1:= h2 t; have g2:= h2 (3 * t); have g3:= h2 (-(6 * t))
            rw [show t + 8 * t = 9 * t by ring] at g1; rw [g1]
            rw [show 3 * t + 8 * t = 11 * t by ring] at g2; rw [g2]
            simp; clear g1 g2
            have g1 : sin (2 * (3 * t)) = 2 * sin (3 * t) * cos (3 * t):= sin_two_mul (3 * t)
            have g2 : sin (2 * t) = 2 * sin t * cos t:= sin_two_mul t
            replace g1 : sin (3 * t) * cos (3 * t) = sin (2 * (3 * t)) / 2:= by linarith
            replace g2 : sin t * cos t = sin (2 * t) / 2:= by linarith
            rw [show √2 ^ k * cos (3 * t) * sin t * sin (3 * t) * cos t = √2 ^ k * (sin t * cos t) * (sin (3 * t) * cos (3 * t)) by ring]
            rw [g1, g2]
            rw [show 2 * (3 * t) = 6 * t by ring]; field_simp
            rw [show (16:ℝ) = 4*4 by norm_num, ← mul_assoc, show (2:ℝ)*2 = 4 by norm_num]
            rw [sin_neg] at g3; simp at g3
            rw [show -(6 * t) + 8 * t = 2 * t by ring] at g3
            rw [mul_right_cancel_iff_of_pos, ← g3]; clear g1 g2 g3
            have g1 : sin (2 * (2 * t)) = 2 * sin (2 * t) * cos (2 * t):= sin_two_mul (2 * t)
            rw [show 2 * (2 * t) = 4 * t by ring] at g1
            replace g1 : sin (2 * t) * cos (2 * t) * 4 = 2 * sin (4 * t):= by linarith
            rw [mul_assoc, mul_assoc]; nth_rw 2 [← mul_assoc]; rw [g1]; clear g1
            have g1 : sin (4 * t) = √2 / 2:= by
                rw [ht]
                rw [show 4 * (π * 3 ^ (k * 4) / 16) = π * 3 ^ (k * 4) / 4 by ring]
                have h3 : ∀ (n : ℕ), (8 : ℤ) ∣ 3 ^ (n * 4) - 1:= by
                    intro n; induction n with
                    | zero => norm_num
                    | succ s ihs =>
                    rw [show (s + 1) * 4 = s * 4 + 4 by omega]
                    rw [show (3 : ℤ) ^ (s * 4 + 4) = 3 ^ (s * 4) * 3 ^ 4 by ring]
                    rw [show (3 : ℤ) ^ 4 = 81 by norm_num]
                    rw [show (3 : ℤ) ^ (s * 4) * 81 - 1 = (3 ^ (s * 4) - 1) * 81 + 80 by ring]
                    omega
                specialize h3 k; rcases h3 with ⟨k_1, h3⟩; rify at h3
                replace h3 : (3 : ℝ) ^ (k * 4) = 8 * ↑k_1 + 1:= by linarith
                rw [show π * 3 ^ (k * 4) / 4 = (π / 4) * 3 ^ (k * 4) by ring, h3]
                rw [show π / 4 * (8 * ↑k_1 + 1) = π * ((8 * ↑k_1 + 1) / 4) by ring]
                have h4 : ((8 : ℝ) * ↑k_1 + 1) / (4 : ℝ) = 2 * ↑k_1 + 1 / 4:= by ring
                rw [h4]
                have h5 : π * ((2 : ℝ) * ↑k_1 + 1 / (4 : ℝ)) = π * (2 * ↑k_1) + π / 4:= by ring
                rw [h5]
                have hkkk : ∃ (k : ℤ), π / 4 = 2 * ↑k * Real.pi + (π * (2 * ↑k_1) + π / 4) ∨ π / 4 = (2 * ↑k + 1) * Real.pi - (π * (2 * ↑k_1) + π / 4):= by
                    use (-k_1); left; simp; ring
                have h6 : sin (π * (2 * ↑k_1) + π / 4) = sin (π / 4):= Real.sin_eq_sin_iff.mpr hkkk
                rw [sin_pi_div_four] at h6
                exact h6
            rw [g1]; ring; simp

        -- 最终步骤：将100分解为4*25并应用引理
        rw [show 100 = 4 * 25 by simp]; specialize h 25
        rw [h, show 25 = 2*12+1 by simp, pow_add, pow_mul, sq_sqrt]
        norm_num; simp