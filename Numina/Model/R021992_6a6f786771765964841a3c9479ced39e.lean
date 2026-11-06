import Mathlib.Tactic

theorem inequalities_599983
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (h : a + b + c = 3) :
    (a^2 + 9) / (2 * a^2 + (b + c)^2) +
    (b^2 + 9) / (2 * b^2 + (c + a)^2) +
    (c^2 + 9) / (2 * c^2 + (a + b)^2) ≤ 5 := by
  have h1 : (a ^ 2 + 9) / (2 * a ^ 2 + (b + c) ^ 2) ≤ (a + 4) / 3 := by
    have h2 : b + c = 3 - a := by linarith
    rw [h2]
    have h3 : (2 * a^2 + (3 - a) ^ 2) > 0 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (a), h]
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (a - 1), sq_nonneg (a + 3), sq_nonneg (a - 3), sq_nonneg (a * (a - 3)), sq_nonneg ((a - 1) * (a - 1)), sq_nonneg (a - 2), sq_nonneg (a * (a - 1))]
  have h4 : (b ^ 2 + 9) / (2 * b^2 + (c + a)^2) ≤ (b + 4) / 3 := by
    have h5 : c + a = 3 - b := by linarith
    rw [h5]
    have h6 : (2 * b^2 + (3 - b) ^ 2) > 0 := by
      nlinarith [sq_nonneg (b - 1), sq_nonneg (b), h]
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (b - 1), sq_nonneg (b + 3), sq_nonneg (b - 3), sq_nonneg (b * (b - 3)), sq_nonneg ((b - 1) * (b - 1)), sq_nonneg (b - 2), sq_nonneg (b * (b - 1))]
  have h7 : (c ^ 2 + 9) / (2 * c^2 + (a + b)^2) ≤ (c + 4) / 3 := by
    have h8 : a + b = 3 - c := by linarith
    rw [h8]
    have h9 : (2 * c^2 + (3 - c) ^ 2) > 0 := by
      nlinarith [sq_nonneg (c - 1), sq_nonneg (c), h]
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (c - 1), sq_nonneg (c + 3), sq_nonneg (c - 3), sq_nonneg (c * (c - 3)), sq_nonneg ((c - 1) * (c - 1)), sq_nonneg (c - 2), sq_nonneg (c * (c - 1))]
  linarith [h1, h4, h7, h]