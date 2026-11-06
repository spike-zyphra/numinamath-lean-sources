import Mathlib

theorem inequalities_66734 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a ≥ b ∧ b ≥ c) (h2 : a + b + c ≤ 1) :
    a^2 + 3 * b^2 + 5 * c^2 ≤ 1 := by
  rcases h1 with ⟨h11, h12⟩
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c), 
    mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
    mul_nonneg (sub_nonneg.mpr h11) (sub_nonneg.mpr h12)]