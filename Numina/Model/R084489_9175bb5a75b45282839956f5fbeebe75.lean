import Mathlib

open Real

theorem inequalities_229499 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a ≤ b + c ∧ b + c ≤ 3 * a) (h2 : 3 * b^2 ≤ a * (a + c) ∧ a * (a + c) ≤ 5 * b^2) :
    (b - 2 * c) / a ≥ -18 / 5 := by
  have h3 : a ≤ b + c := h1.1
  have h4 : b + c ≤ 3 * a := h1.2
  have h5 : 3 * b^2 ≤ a * (a + c) := h2.1
  have h6 : a * (a + c) ≤ 5 * b^2 := h2.2
  
  have h7 : (b - 2 * c) / a ≥ -18 / 5 := by 
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (a - 2 * b), sq_nonneg (a - c), sq_nonneg (b - c),
        mul_pos ha (show 0 < a by linarith),
        mul_pos ha (show 0 < b by linarith),
        mul_pos ha (show 0 < c by linarith),
        mul_pos (show 0 < b by linarith) (show 0 < c by linarith)]
  
  exact h7