import Mathlib

/- Positive real numbers $a, b, c$ satisfy $a^2 + b^2 + c^2 + a + b + c = 6$.  Prove the following inequality:

$$2(\frac{1}{a^2} + \frac{1}{b^2} + \frac{1}{c^2}) \geq 3 + \frac{1}{a} + \frac{1}{b} + \frac{1}{c}$$

[i]Proposed by Oleksii Masalitin[/i]-/
theorem inequalities_41711 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a^2 + b^2 + c^2 + a + b + c = 6) :
    2 * (1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2) ≥ 3 + 1 / a + 1 / b + 1 / c := by
  -- Prove a lemma that could be used a multiple times.
  have h1 (x : ℝ) (hx : 0 < x) : 2 * (1 / x ^ 2) - (1 / x) ≥ 4 - 3 * x := by
    apply le_of_sub_nonneg
    rw [<-ge_iff_le]
    -- It suffices to show that 2 * (1 / x^2) - (1 / x) - (4 - 3 * x) ≥ 0.
    calc
      _ = (3 * x ^ 3 - 4 * x ^ 2 - x + 2) / x ^ 2 := by
        field_simp [hx.ne']
        ring
      _ ≥ 0 := by
        apply div_nonneg
        . -- Show that 3 * x ^ 3 - 4 * x ^ 2 - x + 2 ≥ 0.
          nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 2 / 3)]
        . -- Verify that the denominator is positive.
          positivity
  have h2 := h1 a ha
  have h3 := h1 b hb
  have h4 := h1 c hc
  have h5 : a + b + c ≤ 3 := by
    -- We use a² + b² + c² + a + b + c = 6 and (a - b)² + (b - c)² + (c - a)² ≥ 0.
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  linarith [h5]