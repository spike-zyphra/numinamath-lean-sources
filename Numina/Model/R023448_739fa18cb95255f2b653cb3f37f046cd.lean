import Mathlib

theorem inequalities_198816 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    27 ≤ ((a^2 + a + 1) * (b^2 + b + 1) * (c^2 + c + 1)) / (a * b * c) := by 
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    exact ha
    exact hb
    exact hc
  have h2 : (a^2 + a + 1) / a ≥ 3 := by
    have h3 : a ^ 2 + a + 1 ≥ 3 * a := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (a * 1)]
    have h4 : a > 0 := ha
    have h5 : (a^2 + a + 1) / a ≥ 3 := by
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith
    linarith
  have h3 : (b^2 + b + 1) / b ≥ 3 := by
    have h4 : b ^ 2 + b + 1 ≥ 3 * b := by
      nlinarith [sq_nonneg (b - 1), sq_nonneg (b * 1)]
    have h5 : b > 0 := hb
    have h6 : (b^2 + b + 1) / b ≥ 3 := by
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith
    linarith
  have h4 : (c^2 + c + 1) / c ≥ 3 := by
    have h5 : c ^ 2 + c + 1 ≥ 3 * c := by
      nlinarith [sq_nonneg (c - 1), sq_nonneg (c * 1)]
    have h6 : c > 0 := hc
    have h7 : (c^2 + c + 1) / c ≥ 3 := by
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith
    linarith
  have h5 : ((a^2 + a + 1) * (b^2 + b + 1) * (c^2 + c + 1)) / (a * b * c) =
      ((a^2 + a + 1) / a) * ((b^2 + b + 1) / b) * ((c^2 + c + 1) / c) := by
    field_simp
    <;> ring
  rw [h5]
  have h6 : ((a^2 + a + 1) / a) * ((b^2 + b + 1) / b) * ((c^2 + c + 1) / c) ≥ 27 := by
    have h7 : (a^2 + a + 1) / a ≥ 3 := h2
    have h8 : (b^2 + b + 1) / b ≥ 3 := h3
    have h9 : (c^2 + c + 1) / c ≥ 3 := h4
    have h10 : ((a^2 + a + 1) / a) * ((b^2 + b + 1) / b) ≥ 9 := by
      nlinarith
    have h11 : ((a^2 + a + 1) / a) * ((b^2 + b + 1) / b) * ((c^2 + c + 1) / c) ≥ 27 := by
      nlinarith
    linarith
  linarith [h6]