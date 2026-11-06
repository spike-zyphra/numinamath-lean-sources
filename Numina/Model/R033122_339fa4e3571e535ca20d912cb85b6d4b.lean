import Mathlib

theorem inequalities_159376 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a + b = 1) :
    (a + 1 / a) * (b + 1 / b) ≥ 25 / 4 := by
  have h1 : b = 1 - a := by linarith
  have h4 : (a + 1 / a) * (b + 1 / b) = ((a^2 + 1) * (b^2 + 1)) / (a * b) := by
    have hb1 : b = 1 - a := by linarith
    rw [hb1]
    field_simp [(show a ≠ 0 by linarith), (show (1 - a : ℝ) ≠ 0 by nlinarith)]
    <;> ring
  rw [h4]
  have h5 : (a^2 + 1) * (b^2 + 1) ≥ (25 / 4) * (a * b) := by
    have hb1 : b = 1 - a := by linarith
    rw [hb1]
    nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (a * (1 - a) - 1 / 4), sq_nonneg (a - (1 - a)), sq_nonneg (a * (a - 1 / 2)), sq_nonneg ((1 - a) * (a - 1 / 2)), mul_pos ha (show (0 : ℝ) < 1 - a by nlinarith), sq_nonneg (a * (1 - a) - 1 / 4)]
  have h6 : (a * b) > 0 := by
    have ha1 : a > 0 := by linarith
    have hb1 : b > 0 := by linarith
    nlinarith
  have h7 : ((a^2 + 1) * (b^2 + 1)) / (a * b) ≥ 25 / 4 := by
    have h8 : (a * b) > 0 := by
      nlinarith
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [h5, mul_pos ha hb, mul_pos ha (show b > 0 by linarith), mul_pos (show a > 0 by linarith) hb]
  linarith [h7]