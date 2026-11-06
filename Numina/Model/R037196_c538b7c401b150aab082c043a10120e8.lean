import Mathlib

theorem inequalities_604128 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    a^3 / (a^2 + b^2) + b^3 / (b^2 + c^2) + c^3 / (c^2 + d^2) + d^3 / (d^2 + a^2) ≥
    (a + b + c + d) / 2 := by

  have h1 : a^3 / (a^2 + b^2) = a - (a * b^2 / (a^2 + b^2)) := by
    field_simp
    <;> nlinarith

  have h2 : b^3 / (b^2 + c^2) = b - (b * c^2 / (b^2 + c^2)) := by
    field_simp
    <;> nlinarith

  have h3 : c^3 / (c^2 + d^2) = c - (c * d^2 / (c^2 + d^2)) := by
    field_simp
    <;> nlinarith

  have h4 : d^3 / (d^2 + a^2) = d - (d * a^2 / (d^2 + a^2)) := by
    field_simp
    <;> nlinarith

  rw [h1, h2, h3, h4]

  have h5 : (a * b^2 / (a^2 + b^2)) ≤ b / 2 := by
    have h_pos1 : 0 < a^2 + b^2 := by
      nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (a - b), sq_nonneg (a * b), mul_pos ha hb]

  have h6 : (b * c^2 / (b^2 + c^2)) ≤ c / 2 := by
    have h_pos1 : 0 < b^2 + c^2 := by
      nlinarith [sq_pos_of_pos hb, sq_pos_of_pos hc]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (b - c), sq_nonneg (b * c), mul_pos hb hc]

  have h7 : (c * d^2 / (c^2 + d^2)) ≤ d / 2 := by
    have h_pos1 : 0 < c^2 + d^2 := by
      nlinarith [sq_pos_of_pos hc, sq_pos_of_pos hd]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (c - d), sq_nonneg (c * d), mul_pos hc hd]

  have h8 : (d * a^2 / (d^2 + a^2)) ≤ a / 2 := by
    have h_pos1 : 0 < d^2 + a^2 := by
      nlinarith [sq_pos_of_pos hd, sq_pos_of_pos ha]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (d - a), sq_nonneg (d * a), mul_pos hd ha]

  linarith [h5, h6, h7, h8]