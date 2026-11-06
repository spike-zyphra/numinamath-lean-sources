import Mathlib

/- There are numbers $A$ and $B$ for which  \[\frac A{x-1}+\frac B{x+1}=\frac{x+2}{x^2-1}\] for every number $x\neq\pm1$.  Find $B$. -/
theorem algebra_21906 {A B : ℝ} (h : ∀ x : ℝ, x ≠ 1 ∧ x ≠ -1 → A / (x - 1) + B / (x + 1) = (x + 2) / (x ^ 2 - 1)) :
    B = -1 / 2 := by
        have h1 := h
        -- 代入 x = -2
        specialize h1 (-2) ⟨(by linarith), (by linarith)⟩
        -- 代入 x = 0
        specialize h 0 ⟨(by linarith), (by linarith)⟩
        norm_num at h h1
        linarith
