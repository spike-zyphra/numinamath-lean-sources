import Mathlib

/- There are numbers $A$ and $B$ for which  \[\frac A{x-1}+\frac B{x+1}=\frac{x+2}{x^2-1}\]for every number $x\neq\pm1$.  Find $A-B$. -/
theorem algebra_22017 {A B : ℝ} (h : ∀ x : ℝ, x ≠ 1 ∧ x ≠ -1 → A / (x - 1) + B / (x + 1) = (x + 2) / (x ^ 2 - 1)) :
    A - B = 2 := by
        -- 将 x = 0 代入等式中
        specialize h 0 (by norm_num)
        -- 化简分母中的 x^2 - 1
        simp at h
        -- 对等式进行代数化简
        ring_nf at h
        -- 使用线性算术求解 A - B
        linarith
