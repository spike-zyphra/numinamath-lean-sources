import Mathlib

/- Given $a>0$, $b>0$, $a+b=2$, then the minimum value of $\frac{{{a}^{2}}+{{b}^{2}}}{a+b}$ is ___          ___. -/
theorem algebra_7367 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a + b = 2) :
    (a^2 + b^2) / (a + b) ≥ 1 := by
  -- First, we note that $a + b > 0$ given $a > 0$ and $b > 0$
  have h1 : a + b > 0 := by
    linarith
  -- We can rewrite $b = 2 - a$ from $a + b = 2$
  have h3 : b = 2 - a := by linarith
  -- Show that $a^2 + b^2 \geq 2$.
  have h2 : a^2 + b^2 ≥ 2 := by
    rw [h3]
    -- $a^2 + (2 - a)^2 = 2(a - 1)^2 + 2 \geq 2$
    nlinarith [sq_nonneg (a - 1)]
  -- Multiply both sides of $a^2 + b^2 \geq 2$ by $\frac{1}{a + b}$, which is positive
  have h4 : (a^2 + b^2) / (a + b) ≥ 1 := by
    -- Note that $a + b = 2 > 0$, so $\frac{a + b}{a + b} = 1$
    have h5 : a + b > 0 := h1
    -- Show $\frac{a^2 + b^2}{a + b} \geq \frac{a + b}{a + b} = 1$
    have h6 : (a^2 + b^2) / (a + b) ≥ (a + b) / (a + b) := by
      apply (div_le_div_right h5).mpr 
      linarith [h2, h]
    -- Since $\frac{a + b}{a + b} = 1$, we get $\frac{a^2 + b^2}{a + b} \geq 1$
    have h7 : (a + b) / (a + b) = 1 := by 
      field_simp [h5.ne.symm]
    linarith [h6, h7]
  exact h4