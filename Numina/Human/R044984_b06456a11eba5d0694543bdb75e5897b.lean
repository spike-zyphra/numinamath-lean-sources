import Mathlib

/- 5. Let $a, b, c$ be positive numbers, and $a+b+c=1$, prove: $\frac{a}{1+a^{2}}+\frac{b}{1+b^{2}}+\frac{c}{1+c^{2}} \leqslant \frac{9}{10}$.
(1996 Polish Mathematical Olympiad Problem)-/

theorem inequalities_602273 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c = 1) :
    a / (1 + a ^ 2) + b / (1 + b ^ 2) + c / (1 + c ^ 2) ≤ 9 / 10 := by
  -- Show that x / (1 + x ^ 2) ≤ (3 * (12 * x + 1)) / 50 for any x > 0.
  have hlm (x : ℝ) (hx : 0 < x) : x / (1 + x ^ 2) ≤ (3 * (12 * x + 1)) / 50 := by
    -- Remove the denominators in the inequality.
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    -- It suffices to use the fact that (a - 1 / 3)² ≥ 0.
    nlinarith [sq_nonneg (x - 1 / 3)]
  -- Since a + b + c = 1, by adding the inequalities we get from substituting x = a, b and c respectively into hlm, we get the desired result.
  linarith only [hlm a ha, hlm b hb, hlm c hc, h]