import Mathlib

/- Let $a, b$ and $c$ be positive real numbers satisfying $$\frac{1}{a + 2019}+\frac{1}{b + 2019}+\frac{1}{c + 2019}=\frac{1}{2019}.$$ Prove that $abc \ge 4038^3$. -/
theorem inequalities_64413 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 1 / (a + 2019) + 1 / (b + 2019) + 1 / (c + 2019) = 1 / 2019) :
    a * b * c ≥ 4038 ^ 3 := by
  -- Start by rewriting given equation in terms of factors
  field_simp [add_pos, ha, hb, hc] at h ⊢
  ring_nf at h ⊢
  -- Use substitutive inequality and multiply conditions
  nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos hc ha,
    -- Non-negative square inequality for three terms
    sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]