import Mathlib

theorem algebra_296731 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a^2 + c^2 = 4^2) (h2 : b^2 + c^2 = 5^2) :
    9 < a^2 + b^2 ∧ a^2 + b^2 < 41 := by
  have h3 : a^2 + b^2 < 41 := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc]
  have h4 : 9 < a^2 + b^2 := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc]
  exact ⟨h4, h3⟩