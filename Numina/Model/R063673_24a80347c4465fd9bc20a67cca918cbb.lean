import Mathlib

theorem inequalities_301852 (a b c : ℝ) (ha : a > b) (hb : b > c) :
    0 < 1 / (a - b) + 1 / (b - c) + 1 / (c - a) := by
  have h1 : a - b > 0 := by linarith
  have h2 : b - c > 0 := by linarith
  have h3 : c - a < 0 := by linarith
  have h6 : (a - b) ≠ 0 := by linarith
  have h7 : (b - c) ≠ 0 := by linarith
  have h8 : (c - a) ≠ 0 := by linarith

  have h9 : (a - b) * (b - c) * (c - a) < 0 := by
    apply mul_neg_of_pos_of_neg
    · apply mul_pos
      all_goals linarith
    · linarith

  have h10 : 1 / (a - b) + 1 / (b - c) + 1 / (c - a) =
      ((b - c) * (c - a) + (a - b) * (c - a) + (a - b) * (b - c)) / ((a - b) * (b - c) * (c - a)) := by
    field_simp [h6, h7, h8]
    <;> ring

  rw [h10]

  apply div_pos_of_neg_of_neg
  · nlinarith [sq_pos_of_pos (show 0 < a - b by linarith), sq_pos_of_pos (show 0 < b - c by linarith),
      sq_pos_of_neg (show c - a < 0 by linarith)]
  · linarith