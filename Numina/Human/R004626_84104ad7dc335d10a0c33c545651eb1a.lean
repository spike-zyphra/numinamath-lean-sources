import Mathlib

/- Let $f(x)$ be a function with the property that $f(x)+f\left(\frac{x-1}{3 x-2}\right)=x$ for all real numbers $x$ other $\operatorname{than} \frac{2}{3}$. What is the sum $f(0)+f(1)+f(2) ?$ -/
theorem algebra_290876 {f : ℝ → ℝ} (hf : ∀ x, x ≠ 2 / 3 → f x + f ((x - 1) / (3 * x - 2)) = x) :
    f 0 + f 1 + f 2 = 87 / 40 := by
        --First, show f 1 + f 0 = 1.
        have H1 : f 1 + f 0 = 1 := by
            specialize hf 1
            have : 1 ≠ (2 : ℝ) / (3 : ℝ) := by norm_num
            have : f 1 + f ((1 - 1) / (3 * 1 - 2)) = 1 := by
                apply hf this
            simp at this
            exact this
        --Second, show f 2 + f (1/4) = 2
        have H2 : f 2 + f (1 / 4 : ℝ) = 2 := by
            specialize hf 2
            have : f 2 + f ((2 - 1) / (3 * 2 - 2)) = 2 := by
                apply hf
                norm_num
            ring_nf at this
            exact this
        --Third, show f (1 / 4) + f (3 / 5) = 1 / 4.
        have H3 : f (1 / 4 : ℝ) + f (3 / 5 : ℝ) = (1 / 4 : ℝ) := by
            specialize hf (1 / 4 : ℝ)
            have : f (1 / 4) + f ((1 / 4 - 1) / (3 * (1 / 4) - 2)) = 1 / 4 := by
                apply hf
                norm_num
            ring_nf at this
            exact this
        --Fourth, show f (3 / 5) + f 2 = 3 / 5
        have H4 : f (3 / 5 : ℝ) + f 2 = (3 / 5 : ℝ) := by
            specialize hf (3 / 5 : ℝ)
            have : f (3 / 5) + f ((3 / 5 - 1) / (3 * (3 / 5) - 2)) = 3 / 5 := by
                apply hf
                norm_num
            ring_nf at this
            exact this
        linarith