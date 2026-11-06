import Mathlib

open Real

theorem inequalities_11553 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a ≤ b + c ∧ b + c ≤ 3 * a) (h2 : 3 * b ^ 2 ≤ a * (a + c) ∧ a * (a + c) ≤ 5 * b ^ 2) :
    (b - 2 * c) / a ≥ -18 / 5 := by 
  rcases h1 with ⟨h11, h12⟩
  rcases h2 with ⟨h21, h22⟩
  have h3 : (b - 2 * c) / a ≥ -18 / 5 := by 
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (a - 2 * b + c), sq_nonneg (b - 3 * c), sq_nonneg (a - 3 * b), sq_nonneg (b - c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  exact h3