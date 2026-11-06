import Mathlib

/- Let $f(x) = 2^x.$ Find $\sqrt{f(f(f(f(1))))}.$ -/
theorem algebra_19346 {f : ℝ → ℝ} (hf : f = fun x => 2 ^ x) :
    Real.sqrt (f (f (f (f 1)))) = 256 := by
        rw [hf]        -- 将 f 替换为 λ x => 2^x
        simp          -- 简化表达式
        ring_nf       -- 使用环的标准形式化简
        calc _ = √(256 ^ 2) := by ring_nf    -- 计算得到 √(256^2)
             _ = 256 := Real.sqrt_sq (by linarith)   -- 应用平方根性质：√(a^2) = a，当 a ≥ 0
