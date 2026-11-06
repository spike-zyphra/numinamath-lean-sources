import Mathlib

/-
Let positive real numbers $a, b, c$ satisfy $a^{3}+b^{3}+c^{3}=3$. Prove:
$$
\frac{1}{a^{2}+a+1}+\frac{1}{b^{2}+b+1}+\frac{1}{c^{2}+c+1} \geqslant 1 .
$$
-/
theorem inequalities_299138 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^3 + b^3 + c^3 = 3) :
    1 ≤ 1 / (a^2 + a + 1) + 1 / (b^2 + b + 1) + 1 / (c^2 + c + 1) := by

  -- A auxliary lemma proves that for any positive real number x,
  have h1 : ∀ x : ℝ, 0 < x → 1 / (x^2 + x + 1) ≥ (2 / 3) - (x / 3) := by
    intros x hx
    have h2 : x ^ 2 + x + 1 > 0 := by
      nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (x + 1 / 2)]
    have h3 : 1 / (x^2 + x + 1) ≥ (2 / 3) - (x / 3) := by
      have h4 : x ^ 3 - x ^ 2 - x + 1 ≥ 0 := by
        nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1)]
      have h5 : x^2 + x + 1 > 0 := by nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (x + 1 / 2)]
      have h6 : (2 / 3 - x / 3) ≤ (1) / (x^2 + x + 1) := by
        apply (le_div_iff₀ h5).mpr
        nlinarith
      linarith
    linarith

  -- Apply the lemma to 1 / (a^2 + a + 1), 1 / (b^2 + b + 1), and 1 / (c^2 + c + 1).
  have h2 := h1 a ha
  have h3 := h1 b hb
  have h4 := h1 c hc

  -- The rewrite with h2, h3 and h4, the get LHS ≥ 2 - (a+b+c)/3 ≥ 1
  have h5 : a + b + c ≤ 3 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      sq_nonneg (a + b + c - 3), h, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
  have h6 : 1 ≤ 1 / (a^2 + a + 1) + 1 / (b^2 + b + 1) + 1 / (c^2 + c + 1) := by
    linarith [h2, h3, h4, h5]
  exact h6