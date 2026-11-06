import Mathlib

/- The complex numbers $z$ and $w$ satisfy the system
\begin{align*}
z + \frac{20i}w &= 5+i, \\
w+\frac{12i}z &= -4+10i.
\end{align*}Find the smallest possible value of $\vert zw\vert^2$. -/
theorem algebra_21921 :
    IsLeast {a : ℝ | ∃ z w : ℂ, (a = Complex.abs (z * w) ^ 2) ∧ (z ≠ 0) ∧ (w ≠ 0) ∧ z + 20 * .I / w = 5 + .I ∧ w + 12 * .I / z = -4 + 10 * .I} 40 := by
        simp
        -- 证明分两步：能取等和最小值
        constructor <;>
        simp [lowerBounds]
        .
            -- z = 1 - i, w = 2 + 4 * i时取等
            use (1 - .I)
            use (2 + 4 * .I)
            constructor
            .
                -- |z * w| ^ 2 = 40
                simp [Complex.abs, Complex.normSq]
                norm_num
                rw [show √2 * √20 = √(2 * 20) by refine Eq.symm (Real.sqrt_mul' 2 (by linarith))]
                norm_num
            .
                constructor
                .
                    -- z ≠ 0
                    by_contra!
                    replace this : (1 - Complex.I).re = (0 : ℂ).re:= congrArg Complex.re this
                    norm_num at this
                .
                    -- w ≠ 0
                    constructor
                    .
                        by_contra!
                        replace this : (2 + 4 * Complex.I).re = (0 : ℂ).re:= congrArg Complex.re this
                        norm_num at this
                    .
                        -- z, w 满足题设方程组
                        constructor
                        .
                            have h1 : 2 + 4 * Complex.I ≠ 0:= by
                                by_contra!
                                have h2 : (2 + 4 * Complex.I).re = (0 : ℂ).re:= congrArg Complex.re this
                                norm_num at h2
                            field_simp
                            ring_nf
                            have h2 : Complex.I ^ 2 = -1:= by exact Complex.I_sq
                            rw [h2]
                            ring_nf
                        .
                            have h1 : 1 - Complex.I ≠ 0:= by
                                by_contra!
                                have h2 : (1 - Complex.I).re = (0 : ℂ).re:= congrArg Complex.re this
                                norm_num at h2
                            field_simp
                            ring_nf
                            have h2 : Complex.I ^ 2 = -1:= by exact Complex.I_sq
                            rw [h2]
                            ring_nf
        .
            intro a z w ha hz hw h1 h2
            -- 将 h1 h2 相乘，得到关于 z * w 的方程
            have h3 : (z + 20 * Complex.I / w) * (w + 12 * Complex.I / z) = (5 + Complex.I) * (-4 + 10 * Complex.I):= Mathlib.Tactic.LinearCombination'.mul_pf h1 h2
            clear h1 h2
            field_simp at h3
            rw [show Complex.abs z * Complex.abs w = Complex.abs (z * w) by exact Eq.symm (AbsoluteValue.map_mul Complex.abs z w)] at ha
            let t:= z * w
            -- 引入 t 简化证明
            have ht : t = z * w:= by rfl
            rw [show w * z = z * w by ring] at h3
            ring_nf at h3
            field_simp at h3
            rw [show z ^ 2 * w ^ 2 = (z * w) ^ 2 by ring] at h3
            rw [←ht] at h3
            replace h3 : t ^ 2 + (30 - 14 * .I) * t - 240 = 0:= by linear_combination h3
            -- 解出 t
            replace h3 : (t - 6 - 2 * .I) * (t + 36 - 12 * .I) = 0:= by
                ring_nf
                ring_nf at h3
                field_simp
                linear_combination h3
            replace h3 : t - 6 - 2 * .I = 0 ∨ t + 36 - 12 * .I = 0:= by exact mul_eq_zero.mp h3
            rw [←ht] at ha
            -- 分情况讨论
            rcases h3 with h3 | h3
            .
                replace h3 : t = 6 + 2 * Complex.I:= by linear_combination h3
                rw [ha, h3]
                simp [Complex.abs, Complex.normSq]
                norm_num
            .
                replace h3 : t = -36 + 12 * Complex.I:= by linear_combination h3
                rw [ha, h3]
                simp [Complex.abs, Complex.normSq]
                norm_num
