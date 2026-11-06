import Mathlib.Tactic

theorem inequalities_143252 (a b c : ℝ)
    (h₀ : a + b > c)
    (h₁ : a + c > b)
    (h₂ : b + c > a) :
    2 * (a + b + c) * (a^2 + b^2 + c^2) / 3 > a^3 + b^3 + c^3 + a * b * c := by
  nlinarith [sq_pos_of_pos (show (a + b + c) > 0 by nlinarith), sq_pos_of_pos (show (a + b - c) > 0 by nlinarith), sq_pos_of_pos (show (a + c - b) > 0 by nlinarith), sq_pos_of_pos (show (b + c - a) > 0 by nlinarith)]