import Mathlib

open Real
set_option maxHeartbeats 300000

/- Given that $x,$ $y,$ $z > 0$ and $xyz = 1,$ find the range of all possible values of
\[\frac{x^3 + y^3 + z^3 - x^{-3} - y^{-3} - z^{-3}}{x + y + z - x^{-1} - y^{-1} - z^{-1}}.\]。-/

-- 主定理：证明当满足条件时，表达式的值始终大于27
theorem algebra_20903 (f : ℝ × ℝ × ℝ → ℝ) (hf : f = fun ((x, y, z) : ℝ × ℝ × ℝ) => (x ^ 3 + y ^ 3 + z ^ 3 - x ^ (-3 : ℤ) - y ^ (-3 : ℤ) - z ^ (-3 : ℤ)) / (x + y + z - x ^ (-1 : ℤ) - y ^ (-1 : ℤ) - z ^ (-1 : ℤ))):
    (∀ (x y z : ℝ), 0 < x ∧ 0 < y ∧ 0 < z ∧ x + y + z - x ^ (-1 : ℤ) - y ^ (-1 : ℤ) - z ^ (-1 : ℤ) ≠ 0 ∧ x * y * z = 1 → 27 < f (x, y, z)) := by
            -- 引入变量和条件
            intro x y z ⟨h1, h2, h3, hne0, h4⟩
            simp [hf]
            -- 证明 x y z 均不为 1
            have H : x - 1 ≠ 0 ∧ y - 1 ≠ 0 ∧ z - 1 ≠ 0:= by
                constructor
                .
                    by_contra!
                    replace this : x = 1:= by linarith
                    simp [this] at h4 hne0
                    have g1 : y⁻¹ = z:= by
                        field_simp
                        linarith
                    have g2 : z⁻¹ = y:= by
                        field_simp
                        linarith
                    rw [g1, g2] at hne0
                    have g3 : 1 + y + z - 1 - z - y = 0:= by linarith
                    trivial
                .
                    constructor
                    .
                        by_contra!
                        replace this : y = 1:= by linarith
                        simp [this] at h4 hne0
                        have g1 : z⁻¹ = x:= by
                            field_simp
                            linarith
                        have g2 : x⁻¹ = z:= by
                            field_simp
                            linarith
                        rw [g1, g2] at hne0
                        have g3 : x + 1 + z - z - 1 - x = 0:= by linarith
                        trivial
                    .
                        by_contra!
                        replace this : z = 1:= by linarith
                        simp [this] at h4 hne0
                        have g1 : x⁻¹ = y:= by
                            field_simp
                            linarith
                        have g2 : y⁻¹ = x:= by
                            field_simp
                            linarith
                        rw [g1, g2] at hne0
                        have g3 : x + y + 1 - y - x - 1 = 0:= by linarith
                        trivial
            rcases H with ⟨hxne0, hyne0, hzne0⟩
            -- 证明分子可以写成 (x^3-1)(y^3-1)(z^3-1) 的形式
            have g1 : x ^ 3 + y ^ 3 + z ^ 3 - x ^ (-3 : ℤ) - y ^ (-3 : ℤ) - z ^ (-3 : ℤ) = (x ^ 3 - 1) * (y ^ 3 - 1) * (z ^ 3 - 1):= by
                -- 利用 xyz = 1 证明 x^(-3) = y^3 * z^3
                have hx : x ^ (-3 : ℤ) = y ^ 3 * z ^ 3:= by
                    calc _ = x ^ (-3 : ℤ) * 1 ^ 3:= by ring_nf
                        _ = x ^ (-3 : ℤ) * (x * y * z) ^ 3:= by rw[←h4]
                        _ = (x ^ (-3 : ℤ) * x ^ 3) * (y ^ 3 * z ^ 3):= by ring_nf
                        _ = y ^ 3 * z ^ 3:= by
                            simp
                            field_simp
                            ring_nf
                            calc _ = x ^ 3 * (y ^ 3 * z ^ 3):= by ring_nf
                                _ = (y ^ 3 * z ^ 3) * x ^ 3:= by ring_nf

                -- 类似地证明 y^(-3) = x^3 * z^3
                have hy : y ^ (-3 : ℤ) = x ^ 3 * z ^ 3:= by
                    calc _ = y ^ (-3 : ℤ) * 1 ^ 3:= by ring_nf
                        _ = y ^ (-3 : ℤ) * (x * y * z) ^ 3:= by rw[←h4]
                        _ = (y ^ (-3 : ℤ) * y ^ 3) * (x ^ 3 * z ^ 3):= by ring_nf
                        _ = x ^ 3 * z ^ 3:= by
                            simp
                            field_simp
                            ring_nf
                            calc _ = y ^ 3 * (x ^ 3 * z ^ 3):= by ring_nf
                                _ = (x ^ 3 * z ^ 3) * y ^ 3:= by ring_nf

                -- 类似地证明 z^(-3) = x^3 * y^3
                have hz : z ^ (-3 : ℤ) = x ^ 3 * y ^ 3:= by
                    calc _ = z ^ (-3 : ℤ) * 1 ^ 3:= by ring_nf
                        _ = z ^ (-3 : ℤ) * (x * y * z) ^ 3:= by rw[←h4]
                        _ = (z ^ (-3 : ℤ) * z ^ 3) * (x ^ 3 * y ^ 3):= by ring_nf
                        _ = x ^ 3 * y ^ 3:= by
                            simp
                            field_simp
                            ring_nf
                            calc _ = z ^ 3 * (x ^ 3 * y ^ 3):= by ring_nf
                                _ = (x ^ 3 * y ^ 3) * z ^ 3:= by ring_nf
                rw [hx, hy, hz]

                -- 通过代数运算证明等式成立
                calc _ = x ^ 3 + y ^ 3 + z ^ 3 - y ^ 3 * z ^ 3 - x ^ 3 * z ^ 3 - x ^ 3 * y ^ 3 + (x * y * z) ^ 3 - 1:= by
                        rw [h4]
                        ring_nf
                    _ = x ^ 3 + y ^ 3 + z ^ 3 - y ^ 3 * z ^ 3 - x ^ 3 * z ^ 3 - x ^ 3 * y ^ 3 + x ^ 3 * y ^ 3 * z ^ 3 - 1:= by ring_nf
                    _ = (x ^ 3 - 1) * (y ^ 3 - 1) * (z ^ 3 - 1):= by ring_nf

            -- 证明分母可以写成 (x-1)(y-1)(z-1) 的形式
            have g2 : x + y + z - x ^ (-1 : ℤ) - y ^ (-1 : ℤ) - z ^ (-1 : ℤ) = (x - 1) * (y - 1) * (z - 1):= by
                -- 利用 xyz = 1 证明 x^(-1) = yz
                have hx : x ^ (-1 : ℤ) = y * z:= by
                    calc _ = x ^ (-1 : ℤ) * 1:= by ring_nf
                        _ = x ^ (-1 : ℤ) * (x * y * z):= by rw[←h4]
                        _ = (x ^ (-1 : ℤ) * x) * (y * z):= by ring_nf
                        _ = y * z:= by
                            simp
                            field_simp

                -- 类似地证明 y^(-1) = xz
                have hy : y ^ (-1 : ℤ) = x * z:= by
                    calc _ = y ^ (-1 : ℤ) * 1:= by ring_nf
                        _ = y ^ (-1 : ℤ) * (x * y * z):= by rw[←h4]
                        _ = (y ^ (-1 : ℤ) * y) * (x * z):= by ring_nf
                        _ = x * z:= by
                            simp
                            field_simp

                -- 类似地证明 z^(-1) = xy
                have hz : z ^ (-1 : ℤ) = x * y:= by
                    calc _ = z ^ (-1 : ℤ) * 1:= by ring_nf
                        _ = z ^ (-1 : ℤ) * (x * y * z):= by rw[←h4]
                        _ = (z ^ (-1 : ℤ) * z) * (x * y):= by ring_nf
                        _ = x * y:= by
                            simp
                            field_simp
                rw [hx, hy, hz]
                calc _ = x + y + z - y * z - x * z - x * y + (x * y * z) - 1:= by
                        rw [h4]
                        ring_nf
                    _ = x + y + z - y * z - x * z - x * y + x * y * z - 1:= by ring_nf
                    _ = (x - 1) * (y - 1) * (z - 1):= by ring_nf

            -- 重写表达式，使用更简洁的形式
            replace g1 : x ^ 3 + y ^ 3 + z ^ 3 - (x ^ (3 : ℤ))⁻¹ - (y ^ (3 : ℤ))⁻¹ - (z ^ (3 : ℤ))⁻¹ = (x ^ 3 - 1) * (y ^ 3 - 1) * (z ^ 3 - 1):= by
                rw [←g1]
                simp
            replace g2 : x + y + z - x⁻¹ - y⁻¹ - z⁻¹ = (x - 1) * (y - 1) * (z - 1):= by
                rw [←g2]
                simp
            simp [g1, g2]

            -- 使用立方差公式进行分解
            have hx : x ^ 3 - 1 = (x - 1) * (x ^ 2 + x + 1):= by ring_nf
            have hy : y ^ 3 - 1 = (y - 1) * (y ^ 2 + y + 1):= by ring_nf
            have hz : z ^ 3 - 1 = (z - 1) * (z ^ 2 + z + 1):= by ring_nf
            simp [hx, hy, hz]

            -- 化简分式
            have g3 : (x - 1) * (x ^ 2 + x + 1) * ((y - 1) * (y ^ 2 + y + 1)) * ((z - 1) * (z ^ 2 + z + 1)) / ((x - 1) * (y - 1) * (z - 1)) = (x ^ 2 + x + 1) * (y ^ 2 + y + 1) * (z ^ 2 + z + 1):= by
                have h5 : (x - 1) * (x ^ 2 + x + 1) * ((y - 1) * (y ^ 2 + y + 1)) * ((z - 1) * (z ^ 2 + z + 1)) = ((x ^ 2 + x + 1) * (y ^ 2 + y + 1) * (z ^ 2 + z + 1)) * ((x - 1) * (y - 1) * (z - 1)):= by ring_nf
                rw [h5]
                have h6 : (x - 1) * (y - 1) * (z - 1) ≠ 0:= by
                    by_contra! H
                    have h7 : (x - 1) * (y - 1) ≠ 0:= mul_ne_zero hxne0 hyne0
                    have h8 : (x - 1) * (y - 1) * (z - 1) ≠ 0:= mul_ne_zero h7 hzne0
                    trivial
                have h7 : ((x - 1) * (y - 1) * (z - 1)) / ((x - 1) * (y - 1) * (z - 1)) = 1:= by field_simp
                field_simp [h6, h7]
            rw [g3]
            clear hx hy hz g1 g2 g3

            -- 证明一系列不等式
            have hx1 : (x - 1) ^ 2 ≥ 0:= by apply sq_nonneg (x - 1)
            have hy1 : (y - 1) ^ 2 ≥ 0:= by apply sq_nonneg (y - 1)
            have hz1 : (z - 1) ^ 2 ≥ 0:= by apply sq_nonneg (z - 1)
            replace hx1 : (x - 1) ^ 2 > 0:= by
                by_contra! H
                replace H : (x - 1) ^ 2 = 0:= by linarith
                replace H : x - 1 = 0:= by exact pow_eq_zero H
                trivial
            replace hy1 : (y - 1) ^ 2 > 0:= by
                by_contra! H
                replace H : (y - 1) ^ 2 = 0:= by linarith
                replace H : y - 1 = 0:= by exact pow_eq_zero H
                trivial
            replace hz1 : (z - 1) ^ 2 > 0:= by
                by_contra! H
                replace H : (z - 1) ^ 2 = 0:= by linarith
                replace H : z - 1 = 0:= by exact pow_eq_zero H
                trivial

            -- 证明二次式的正性
            have hx2 : x ^ 2 + x + 1 > 0:= by linarith
            have hy2 : y ^ 2 + y + 1 > 0:= by linarith
            have hz2 : z ^ 2 + z + 1 > 0:= by linarith

            -- 证明一系列乘积的正性
            have t1 : (x - 1) ^ 2 * (y ^ 2 + y + 1) > 0:= by nlinarith only [hx1, hy2]
            replace t1 : (x - 1) ^ 2 * (y ^ 2 + y + 1) * (z ^ 2 + z + 1) > 0:= by nlinarith only [t1, hz2]
            have t2 : 3 * x * (y - 1) ^ 2 > 0:= by nlinarith only [h1, hy1]
            replace t2 : 3 * x * (y - 1) ^ 2 * (z ^ 2 + z + 1) > 0:= by nlinarith only [t2, hz2]
            have t3 : 3 * x * 3 * y > 0:= by nlinarith only [h1, h2]
            replace t3 : 3 * x * 3 * y * (z - 1) ^ 2 > 0:= by nlinarith only [t3, hz1]

            
            linarith
