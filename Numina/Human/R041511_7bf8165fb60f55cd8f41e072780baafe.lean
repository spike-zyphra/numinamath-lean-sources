import Mathlib

/-Suppose $a$, $b,$ and $c$ are positive numbers satisfying: \begin{align*}
a^2/b &= 1, \\
b^2/c &= 2, \text{ and}\\
c^2/a &= 3.
\end{align*} Find $a$.-/
theorem algebra_14147 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h1 : a^2 / b = 1) (h2 : b^2 / c = 2) (h3 : c^2 / a = 3) :
  a = 12 ^ ((1 : ℝ) / 7) := by
    -- Notice that multiplying all three of the original equations together tells us that $(a^2b^2c^2)/(abc) = 6$, which implies $abc=6$.
    have c1 : a * b * c = 6 := by
      have : a * b * c = (a^2 / b) * (b^2 / c) * (c^2 / a) := by
        field_simp; ring_nf
      rw [this, h1, h2, h3]
      ring
    have hb : b = a^2 := by field_simp at h1; exact h1.symm
    have hc : c = √(3*a) := by
      field_simp at h3
      apply_fun (√ ·) at h3
      rw [Real.sqrt_sq (le_of_lt hc)] at h3
      exact h3
    simp [hb, hc] at c1
    -- Rewriting the first and third equations as $b = a^2$ and $c = \sqrt{3a}$ and plugging these into $abc=6$ yields $a \cdot a^2\cdot \sqrt{3a} = 6$. 
    have c2 : 3 * a^7 = 36 := by
      apply_fun (·^2) at c1
      simp [mul_pow, Real.sq_sqrt (le_of_lt ha)] at c1
      ring_nf at c1
      linarith
    replace c2 : a^(7:ℝ) = 12 := by
      have : a^7 = 12 := by linarith
      norm_cast
    -- By squaring both sides of the equation, we obtain $3a^7 = 36 \Rightarrow a = \boxed{12^{1/7}}$.
    apply_fun (·^((1:ℝ) / 7)) at c2
    rw [←c2, ←Real.rpow_mul (le_of_lt ha)]
    simp
