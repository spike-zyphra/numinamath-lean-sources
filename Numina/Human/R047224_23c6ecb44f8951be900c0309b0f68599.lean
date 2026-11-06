import Mathlib

/-
$a,b,c \geq-3/4$ and $a+b+c=1$. Show that: $\frac{a}{1+a^{2}}+\frac{b}{1+b^{2}}+\frac{c}{1+c^{2}}\leq \frac{9}{10}$
-/
theorem inequalities_79577 (a b c : ℝ) (ha : -3 / 4 ≤ a) (hb : -3 / 4 ≤ b) (hc : -3 / 4 ≤ c)
    (h : a + b + c = 1) :
    a / (1 + a ^ 2) + b / (1 + b ^ 2) + c / (1 + c ^ 2) ≤ 9 / 10 := by
  have h2 : a / (1 + a^2) + b / (1 + b^2) + c / (1 + c^2) ≤ 9 / 10 := by
    have h3 : a / (1 + a^2) ≤ 3 / 10 + 18 / 25 * (a - 1 / 3) := by
      have h4 : 36 * a^3 + 3 * a^2 - 14 * a + 3 ≥ 0 := by
        nlinarith [sq_nonneg (a + 3 / 4), sq_nonneg (a - 1 / 3), sq_nonneg (a - 1), sq_nonneg (a - 5 / 2)]
      have h5 : 1 + a^2 > 0 := by nlinarith
      have h6 : a ≤ (3 / 10 + 18 / 25 * (a - 1 / 3)) * (1 + a^2) := by
        nlinarith [sq_nonneg (a - 1 / 3), sq_nonneg (a + 3 / 4), sq_nonneg (a - 5 / 2), sq_nonneg (a - 1), sq_nonneg (a + 3 / 4), sq_nonneg (a - 1 / 3)]
      apply (div_le_iff₀ h5).mpr
      nlinarith
    have h7 : b / (1 + b^2) ≤ 3 / 10 + 18 / 25 * (b - 1 / 3) := by
      have h8 : 36 * b^3 + 3 * b^2 - 14 * b + 3 ≥ 0 := by
        nlinarith [sq_nonneg (b + 3 / 4), sq_nonneg (b - 1 / 3), sq_nonneg (b - 1), sq_nonneg (b - 5 / 2)]
      have h9 : 1 + b^2 > 0 := by nlinarith
      have h10 : b ≤ (3 / 10 + 18 / 25 * (b - 1 / 3)) * (1 + b^2) := by
        nlinarith [sq_nonneg (b - 1 / 3), sq_nonneg (b + 3 / 4), sq_nonneg (b - 5 / 2), sq_nonneg (b - 1), sq_nonneg (b + 3 / 4), sq_nonneg (b - 1 / 3)]
      apply (div_le_iff₀ h9).mpr
      nlinarith
    have h11 : c / (1 + c^2) ≤ 3 / 10 + 18 / 25 * (c - 1 / 3) := by
      have h12 : 36 * c^3 + 3 * c^2 - 14 * c + 3 ≥ 0 := by
        nlinarith [sq_nonneg (c + 3 / 4), sq_nonneg (c - 1 / 3), sq_nonneg (c - 1), sq_nonneg (c - 5 / 2)]
      have h13 : 1 + c^2 > 0 := by nlinarith
      have h14 : c ≤ (3 / 10 + 18 / 25 * (c - 1 / 3)) * (1 + c^2) := by
        nlinarith [sq_nonneg (c - 1 / 3), sq_nonneg (c + 3 / 4), sq_nonneg (c - 5 / 2), sq_nonneg (c - 1), sq_nonneg (c + 3 / 4), sq_nonneg (c - 1 / 3)]
      apply (div_le_iff₀ h13).mpr
      nlinarith
    linarith [h3, h7, h11, h]
  linarith [h2]