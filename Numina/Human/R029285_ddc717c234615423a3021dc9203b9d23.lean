import Mathlib

open Set Real

/- What is the range of the function $$f(x) = \frac{1}{1-x}~?$$ Express your answer in interval notation. -/
theorem algebra_21392 (f : ℝ → ℝ) (hf : f = fun x => 1 / (1 - x)) :
    image f {x | x ≠ 1} = {y | y ≠ 0} := by
        -- 简化目标，展开image定义
        simp [image]
        rw [hf]
        simp

        -- 证明第一个包含关系：f的像集是非零实数的子集
        have h1 : {x | ∃ (a : ℝ), ¬a = 1 ∧ (1 - a)⁻¹ = x} ⊆ {y | ¬y = 0} := by
            intro x hx  -- 引入任意元素x及其属于像集的假设
            simp at hx
            rcases hx with ⟨y, hy1, hy2⟩  -- 解构存在性证明
            simp
            -- 使用反证法证明x≠0
            by_contra h2
            rw [h2] at hy2
            simp at hy2
            replace hy2 : y = 1 := by linarith
            trivial

        -- 证明第二个包含关系：非零实数集是f的像集的子集
        have h2 : {y | ¬y = 0} ⊆ {x | ∃ (a : ℝ), ¬a = 1 ∧ (1 - a)⁻¹ = x} := by
            intro x hx  -- 引入任意非零实数x
            simp
            simp at hx
            -- 构造原像：对于任意y≠0，取x=1-1/y作为原像
            use 1 - x⁻¹
            constructor
            . -- 证明构造的原像不等于1
                by_contra h2
                simp at h2
                trivial
            . -- 证明f(1-1/y)=y
                field_simp

        -- 由两个子集关系证明集合相等
        exact Subset.antisymm h1 h2
