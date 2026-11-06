import Mathlib

/- 2. For positive numbers $a, b, c$, it is known that $\frac{1}{a}+\frac{1}{b}+\frac{1}{c} \geqslant a+b+c$. Prove that $a+b+c \geqslant 3 a b c$. -/
theorem inequalities_281417 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 1 / a + 1 / b + 1 / c ≥ a + b + c) : 3 * a * b * c ≤ a + b + c := by
  --show 0 < a * b * c.
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    exact ha
    exact hb
    exact hc
  --show 1 / a + 1 / b + 1 / c = (b * c + a * c + a * b) / (a * b * c)
  have h2 : 1 / a + 1 / b + 1 / c = (b * c + a * c + a * b) / (a * b * c) := by
    field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt hc]
    ring
  rw [h2] at h
  --show  b * c + a * c + a * b ≥ (a * b * c) * (a + b + c)
  have h3 : b * c + a * c + a * b ≥ (a * b * c) * (a + b + c) := by
    have pos1 : 0 < a * b * c := h1
    have h4 : (b * c + a * c + a * b) / (a * b * c) ≥ a + b + c := by linarith
    have h5 : b * c + a * c + a * b ≥ (a * b * c) * (a + b + c) := by
      apply (le_div_iff₀ (by positivity)).mp at h4
      linarith
    linarith
  nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
            sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
            mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]