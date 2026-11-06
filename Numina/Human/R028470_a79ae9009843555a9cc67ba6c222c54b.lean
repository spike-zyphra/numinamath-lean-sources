import Mathlib

open Real Set
open scoped BigOperators

/- The smallest distance between the origin and a point on the graph of $y=\frac{1}{2}x^2-9$ can be expressed as $a$.  Find $a^2$. -/
theorem algebra_18945 (f : ℝ → ℝ) (hf : f = λ x => (1 / 2) * x ^ 2 - 9) :
    IsLeast {d | ∃ x y, d = x ^ 2 + y ^ 2 ∧ y = f x} 17 := by
        -- 构造证明，分为两部分：存在性和最小性
        constructor <;>
        simp [lowerBounds]
        . -- 第一部分：证明存在一个点，其到原点的距离的平方等于17
            rw [hf]
            simp
            norm_num
            use 4    -- 取 x = 4 时
            norm_num  -- 计算得到结果
        . -- 第二部分：证明17是最小值
            intro a
            rw [hf]
            simp
            field_simp
            norm_num
            -- 证明对任意点，到原点的距离平方都大于等于17
            suffices h : (a ^ 2 * 4 + (a ^ 2 - 18) ^ 2) / 4 ≥ 17 by linarith
            -- 通过代数变形证明
            calc _ = ((a ^ 2) ^ 2 - 32 * a ^ 2 + 324) / 4 := by ring
                 _ = ((a ^ 2 - 16) ^ 2 + 68) / 4 := by ring
                 _ ≥ 68 / 4 := by
                    -- 利用平方非负性
                    have _ : (a ^ 2 - 16) ^ 2 ≥ 0 := by
                        apply sq_nonneg
                    linarith
                 _ = 17 := by norm_num

