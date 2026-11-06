import Mathlib

/- Given real numbers $a \gt 0$, $b \gt 0$, simplify: $\frac{{{a^{\frac{3}{2}}}{b^{\frac{5}{2}}}}}{{\sqrt{ab}}}=\_\_\_\_\_\_$. -/
theorem algebra_9262 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a ^ ((3 : ℝ) / 2) * b ^ ((5 : ℝ) / 2) / Real.sqrt (a * b) = a * b ^ 2 := by
    -- First, recall that $\sqrt{ab} = a^{\frac{1}{2}}b^{\frac{1}{2}}$. This allows us to rewrite the denominator as a product of $a$ and $b$ raised to the power of $\frac{1}{2}$.
    rw [Real.sqrt_eq_rpow]
    field_simp
    rw [Real.mul_rpow]
    swap; linarith
    swap; linarith
    rw [show a * b ^ 2 * (a ^ ((1 : ℝ) / 2) * b ^ ((1 : ℝ) / 2)) = a * a ^ ((1: ℝ) / 2) * b ^ 2 * b ^ ((1: ℝ) / 2) by ring_nf]
    rw [show a * a ^ ((1: ℝ) / 2) * b ^ 2 * b ^ ((1: ℝ) / 2) = a ^ (1 : ℝ) * a ^ ((1: ℝ) / 2) * (b ^ 2 * b ^ ((1: ℝ) / 2)) by field_simp; ring_nf]
    -- Using the property that $x^mx^n = x^{m+n}$ for any real number $x$ and any real numbers $m$ and $n$, we can simplify the expression by adding the exponents of $a$ and $b$:
    rw [← Real.rpow_add]
    rw [show b ^ 2 = b ^ (2 : ℝ) by simp]
    rw [← Real.rpow_add]
    -- Therefore, the simplified form of the given expression is $\boxed{ab^2}$.
    norm_num
    repeat linarith
