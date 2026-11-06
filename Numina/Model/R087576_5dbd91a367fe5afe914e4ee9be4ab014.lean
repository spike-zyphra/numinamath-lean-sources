import Mathlib

theorem inequalities_601836 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^3 + b^3 + c^3 = 3) :
    1 ≤ 1 / (a^2 + a + 1) + 1 / (b^2 + b + 1) + 1 / (c^2 + c + 1) := by
  have h1 : 1 / (a^2 + a + 1) ≥ (4 - a^3) / 9 := by
    apply (le_div_iff₀ (by positivity)).mpr
    suffices (4 - a^3) * (a^2 + a + 1) ≤ 9 by linarith
    nlinarith [sq_nonneg (a^2 - 1), sq_nonneg (a - 1), sq_nonneg (a + 1), sq_nonneg (a^3 - 1), sq_nonneg (a^3 + a - 2), sq_nonneg (a^2 + a - 2)]
  have h2 : 1 / (b^2 + b + 1) ≥ (4 - b^3) / 9 := by
    apply (le_div_iff₀ (by positivity)).mpr
    suffices (4 - b^3) * (b^2 + b + 1) ≤ 9 by linarith
    nlinarith [sq_nonneg (b^2 - 1), sq_nonneg (b - 1), sq_nonneg (b + 1), sq_nonneg (b^3 - 1), sq_nonneg (b^3 + b - 2), sq_nonneg (b^2 + b - 2)]
  have h3 : 1 / (c^2 + c + 1) ≥ (4 - c^3) / 9 := by
    apply (le_div_iff₀ (by positivity)).mpr
    suffices (4 - c^3) * (c^2 + c + 1) ≤ 9 by linarith
    nlinarith [sq_nonneg (c^2 - 1), sq_nonneg (c - 1), sq_nonneg (c + 1), sq_nonneg (c^3 - 1), sq_nonneg (c^3 + c - 2), sq_nonneg (c^2 + c - 2)]
  have h4 : 1 / (a^2 + a + 1) + 1 / (b^2 + b + 1) + 1 / (c^2 + c + 1) ≥ (4 - a^3) / 9 + (4 - b^3) / 9 + (4 - c^3) / 9 := by linarith [h1, h2, h3]
  have h5 : (4 - a^3) / 9 + (4 - b^3) / 9 + (4 - c^3) / 9 = 1 := by
    linarith [h]
  linarith [h4, h5]