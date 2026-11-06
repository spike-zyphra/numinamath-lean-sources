import Mathlib

theorem algebra_192095 (a b c : ℝ) (ha : a > b) (hb : b > c) :
    0 < 1 / (a - b) + 1 / (b - c) + 1 / (c - a) := by
  have h1 : a - b > 0 := by linarith
  have h2 : b - c > 0 := by linarith
  have h3 : a - c > 0 := by linarith
  have h4 : c - a < 0 := by linarith
  have pos1 : (a - b) > 0 := h1
  have pos2 : (b - c) > 0 := h2
  have pos3 : (a - c) > 0 := by linarith
  have pos4 : (a - b) * (b - c) * (a - c) > 0 := by positivity
  have pos5 : (b - c) * (a - c) + (a - b) * (a - c) - (a - b) * (b - c) > 0 := by
    nlinarith [sq_pos_of_pos (show a - b > 0 by linarith), sq_pos_of_pos (show b - c > 0 by linarith),
      sq_pos_of_pos (show a - c > 0 by linarith),
      sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      mul_pos (show a - b > 0 by linarith) (show b - c > 0 by linarith),
      mul_pos (show a - b > 0 by linarith) (show a - c > 0 by linarith),
      mul_pos (show b - c > 0 by linarith) (show a - c > 0 by linarith)
      ]
  have h5 : 1 / (a - b) + 1 / (b - c) + 1 / (c - a) =
      ( ( (b - c) * (a - c) + (a - b) * (a - c) - (a - b) * (b - c) ) ) / ( (a - b) * (b - c) * (a - c) ) := by
    field_simp [(show a - b ≠ 0 by linarith), (show b - c ≠ 0 by linarith), (show c - a ≠ 0 by linarith)]
    ring
  rw [h5]
  apply div_pos
  exact pos5
  exact pos4