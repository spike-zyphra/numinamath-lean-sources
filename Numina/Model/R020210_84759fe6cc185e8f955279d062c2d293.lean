import Mathlib

theorem inequalities_234202 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a ≥ b ∧ b ≥ c) (h2 : a + b + c ≤ 1) :
    a^2 + 3 * b^2 + 5 * c^2 ≤ 1 := by
  have h3 : a ≥ b := h1.1
  have h4 : b ≥ c := h1.2
  have hb6 : b ^ 2 + 2 * c ^ 2 - a * b - a * c - b * c ≤ 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c), 
        mul_nonneg (sub_nonneg.mpr h3) (sub_nonneg.mpr h4) ]
  have eq : a^2 + 3 * b^2 + 5 * c^2 - (a + b + c) ^ 2 = 2 * (b ^ 2 + 2 * c ^ 2 - a * b - a * c - b * c) := by
    nlinarith 
  have h7 : a^2 + 3 * b^2 + 5 * c^2 ≤ (a + b + c) ^ 2 := by 
    nlinarith [eq, hb6]
  have h8 : (a + b + c) ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (a + b + c - 1)]
  linarith [h7, h8]