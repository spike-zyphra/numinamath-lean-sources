import Mathlib

theorem inequalities_259385 (a b c : ℝ) (ha : 0 < c) (hc : c < b) (hb : b < a) :
    a^4 * b + b^4 * c + c^4 * a > a * b^4 + b * c^4 + c * a^4 := by
  have h1 : 0 < c := ha
  have h2 : 0 < b := by linarith
  have h3 : 0 < a := by linarith
  have h4 : a > b := by linarith
  have h5 : b > c := by linarith
  have h6 : a > c := by linarith
  have h7 : a^4 * b + b^4 * c + c^4 * a - (a * b^4 + b * c^4 + c * a^4) > 0 := by
    have h71 : 0 < (a - b) * (b - c) * (a - c) := by
      have h14 : 0 < (a - b) := by linarith
      have h15 : 0 < (b - c) := by linarith
      have h16 : 0 < (a - c) := by linarith
      positivity
    have h72 : a^4 * b + b^4 * c + c^4 * a - (a * b^4 + b * c^4 + c * a^4) =
        (a - b) * (b - c) * (a - c) * (a^2 + a * b + b^2 + b * c + c^2 + c * a) := by
      nlinarith [sq_pos_of_pos h1, sq_pos_of_pos h2, sq_pos_of_pos h3, sq_pos_of_pos (show 0 < a - b by linarith), sq_pos_of_pos (show 0 < b - c by linarith)]
    rw [h72]
    have h73 : 0 < (a - b) * (b - c) * (a - c) := h71
    have h74 : 0 < a^2 + a * b + b^2 + b * c + c^2 + c * a := by
      positivity
    apply mul_pos
    . exact h71
    . linarith
  linarith