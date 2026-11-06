import Mathlib

theorem inequalities_598688 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    (a^3 + b^3 + c^3) / (a + b + c) + (b^3 + c^3 + d^3) / (b + c + d) +
    (c^3 + d^3 + a^3) / (c + d + a) + (d^3 + a^3 + b^3) / (d + a + b) ≥
    a^2 + b^2 + c^2 + d^2 := by
  have h1 : 0 < a + b + c := by positivity
  have h2 : 0 < b + c + d := by positivity
  have h3 : 0 < c + d + a := by positivity
  have h4 : 0 < d + a + b := by positivity
  have eq4 : (a^3 + b^3 + c^3) / (a + b + c) + (b^3 + c^3 + d^3) / (b + c + d) +
      (c^3 + d^3 + a^3) / (c + d + a) + (d^3 + a^3 + b^3) / (d + a + b) - (a^2 + b^2 + c^2 + d^2) ≥ 0 := by
    have h1a : (a ^ 3 + b ^ 3 + c ^ 3) / (a + b + c) ≥ (a ^ 2 + b ^ 2 + c ^ 2) / 3 := by
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    have h1b : (b^3 + c^3 + d^3) / (b + c + d) ≥ (b^2 + c^2 + d^2) / 3 := by
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith [sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d),
        mul_pos hb hc, mul_pos hb hd, mul_pos hc hd]
    have h1c : (c^3 + d^3 + a^3) / (c + d + a) ≥ (c^2 + d^2 + a^2) / 3 := by
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith [sq_nonneg (c - d), sq_nonneg (c - a), sq_nonneg (d - a),
        mul_pos hc hd, mul_pos hc ha, mul_pos hd ha]
    have h1d : (d^3 + a^3 + b^3) / (d + a + b) ≥ (d^2 + a^2 + b^2) / 3 := by
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith [sq_nonneg (d - a), sq_nonneg (d - b), sq_nonneg (a - b),
        mul_pos hd ha, mul_pos hd hb, mul_pos ha hb]
    have h32a : (a ^ 3 + b ^ 3 + c ^ 3) / (a + b + c) + (b^3 + c^3 + d^3) / (b + c + d) + (c^3 + d^3 + a^3) / (c + d + a) + (d^3 + a^3 + b^3) / (d + a + b) ≥ (a^2 + b^2 + c^2)/3 + (b^2 + c^2 + d^2)/3 + (c^2 + d^2 + a^2)/3 + (d^2 + a^2 + b^2)/3 := by
      linarith [h1a, h1b, h1c, h1d]
    have h32b : (a^2 + b^2 + c^2)/3 + (b^2 + c^2 + d^2)/3 + (c^2 + d^2 + a^2)/3 + (d^2 + a^2 + b^2)/3 = a^2 + b^2 + c^2 + d^2 := by
      linarith
    have h32c : (a ^ 3 + b ^ 3 + c ^ 3) / (a + b + c) + (b^3 + c^3 + d^3) / (b + c + d) + (c^3 + d^3 + a^3) / (c + d + a) + (d^3 + a^3 + b^3) / (d + a + b) - (a^2 + b^2 + c^2 + d^2) ≥ 0 := by
      linarith [h32a, h32b]
    exact h32c
  linarith [eq4]