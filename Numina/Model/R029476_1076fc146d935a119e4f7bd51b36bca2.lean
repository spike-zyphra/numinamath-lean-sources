import Mathlib

theorem algebra_304974 (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : ∃ x y, x > 0 ∧ y > 0 ∧ x^2 - 3 * a * x + 2 * b = 0 ∧ y^2 - 3 * a * y + 2 * b = 0)
    (h2 : ∃ x y, x > 0 ∧ y > 0 ∧ x^2 - 3 * b * x + 2 * c = 0 ∧ y^2 - 3 * b * y + 2 * c = 0)
    (h3 : ∃ x y, x > 0 ∧ y > 0 ∧ x^2 - 3 * c * x + 2 * a = 0 ∧ y^2 - 3 * c * y + 2 * a = 0) :
    (a, b, c) = (1, 1, 1) := by
  rcases h1 with ⟨x, y, hx_pos, hy_pos, h1x, h1y⟩
  rcases h2 with ⟨u, v, hu_pos, hv_pos, h2u, h2v⟩
  rcases h3 with ⟨s, t, hs_pos, ht_pos, h3s, h3t⟩
  have h4 : x * y = 2 * b := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - 3 * a), sq_nonneg (y - 3 * a), mul_pos (show 0 < x by omega) (show 0 < y by omega)]
  have h5 : u * v = 2 * c := by
    nlinarith [sq_nonneg (u - v), sq_nonneg (u - 3 * b), sq_nonneg (v - 3 * b), mul_pos (show 0 < u by omega) (show 0 < v by omega)]
  have h6 : s * t = 2 * a := by
    nlinarith [sq_nonneg (s - t), sq_nonneg (s - 3 * c), sq_nonneg (t - 3 * c), mul_pos (show 0 < s by omega) (show 0 < t by omega)]
  have h7 : a ≤ 2 := by
    nlinarith [h4, h5, h6, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, mul_pos (show 0 < x by omega) (show 0 < y by omega), mul_pos (show 0 < u by omega) (show 0 < v by omega), mul_pos (show 0 < s by omega) (show 0 < t by omega)]
  have h8 : b ≤ 2 := by
    nlinarith [h4, h5, h6, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, mul_pos (show 0 < x by omega) (show 0 < y by omega), mul_pos (show 0 < u by omega) (show 0 < v by omega), mul_pos (show 0 < s by omega) (show 0 < t by omega)]
  have h9 : c ≤ 2 := by
    nlinarith [h4, h5, h6, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, mul_pos (show 0 < x by omega) (show 0 < y by omega), mul_pos (show 0 < u by omega) (show 0 < v by omega), mul_pos (show 0 < s by omega) (show 0 < t by omega)]
  interval_cases a <;> interval_cases b <;> interval_cases c <;> norm_num [Prod.ext_iff] at *
  <;> omega