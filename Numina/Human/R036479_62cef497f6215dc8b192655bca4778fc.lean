import Mathlib

/- Let $a,$ $b,$ and $c$ be nonzero real numbers such that $\frac{1}{a} + \frac{1}{b} + \frac{1}{c} = 0.$  Compute
\[\frac{bc}{a^2} + \frac{ac}{b^2} + \frac{ab}{c^2}.\] -/
theorem algebra_22181 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : 1 / a + 1 / b + 1 / c = 0) :
    b * c / a ^ 2 + a * c / b ^ 2 + a * b / c ^ 2 = 3 := by
        -- 引入新变量简化表达式
        let x:= 1 / a
        let y:= 1 / b
        let z:= 1 / c
        -- 证明这些新变量的定义
        have hx : x = 1 / a:= by rfl
        have hy : y = 1 / b:= by rfl
        have hz : z = 1 / c:= by rfl
        -- 证明 x + y + z = 0
        have h1 : x + y + z = 0:= by linarith
        -- 使用立方和公式：x³ + y³ + z³ - 3xyz = (x + y + z)(x² + y² + z² - xy - yz - zx)
        have h2 : x ^ 3 + y ^ 3 + z ^ 3 - 3 * x * y * z = 0:= by
            calc _ = (x + y + z) * (x ^ 2 + y ^ 2 + z ^ 2 - x * y - y * z - z * x):= by ring_nf
                 _ = 0 * (x ^ 2 + y ^ 2 + z ^ 2 - x * y - y * z - z * x):= by rw [h1]
                 _ = 0:= by ring
        -- 推导出 x³ + y³ + z³ = 3xyz
        replace h2 : x ^ 3 + y ^ 3 + z ^ 3 = 3 * x * y * z:= by linarith
        -- 将 x, y, z 替换回原始表达式
        rw [hx, hy, hz] at h2
        -- 最终计算
        calc _ =  (a * b * c) / a ^ 3 + (a * b * c) / b ^ 3 + (a * b * c) / c ^ 3:= by
                    field_simp
                    ring_nf
             -- 重写为统一形式
             _ = (a * b * c) * ((1 / a) ^ 3 + (1 / b) ^ 3 + (1 / c) ^ 3):= by ring_nf
             -- 使用之前证明的等式
             _ = (a * b * c) * (3 * (1 / a) * (1 / b) * (1 / c)):= by rw [h2]
             -- 最终简化得到结果 3
             _ = 3:= by field_simp
