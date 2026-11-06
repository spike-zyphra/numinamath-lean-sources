import Mathlib


theorem inequalities_601958
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (habc : a * b * c = 1) :
    (a - 1 + 1 / b) * (b - 1 + 1 / c) * (c - 1 + 1 / a) ≤ 1 := by
  have h2 : (a - 1 + 1 / b) * (b - 1 + 1 / c) * (c - 1 + 1 / a) = ((a * b - b + 1) * (b * c - c + 1) * (c * a - a + 1)) / (a * b * c) := by
    field_simp [hb.ne.symm, hc.ne.symm, ha.ne.symm]
    ring
  rw [h2]

  have h3 : ((a * b - b + 1) * (b * c - c + 1) * (c * a - a + 1) ) ≤ (a * b * c : ℝ) := by
    nlinarith [sq_nonneg (a * b - b + 1 - 1 : ℝ), sq_nonneg (b * c - c + 1 - 1 : ℝ), sq_nonneg (c * a - a + 1 - 1 : ℝ),
      sq_nonneg (a * b * c - 1 : ℝ),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
      mul_nonneg (show 0 ≤ a * b by positivity) (show 0 ≤ b * c by positivity), 
      mul_nonneg (show 0 ≤ b * c by positivity) (show 0 ≤ c * a by positivity), 
      mul_nonneg (show 0 ≤ c * a by positivity) (show 0 ≤ a * b by positivity)]
  have h4 : (a * b * c : ℝ) > 0 := by
    positivity
  apply (div_le_iff₀ (by positivity)).mpr
  linarith