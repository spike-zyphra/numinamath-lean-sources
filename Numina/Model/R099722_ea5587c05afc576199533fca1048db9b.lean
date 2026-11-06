import Mathlib

theorem algebra_300355 {a b : ℝ} (ha : 0 < b) (hb : b < a) (h : 0 < a ∧ a < 1)
    (x : ℝ) (hx : x = (1 - a) * (1 + b)) :
    x < (1 - (a + b) / 2) * (1 + (a + b) / 2) ∧
    x < (1 - b) * (1 + a) := by
  have h1 : x < (1 - (a + b) / 2) * (1 + (a + b) / 2) := by
    rw [hx]
    nlinarith [sq_pos_of_pos (show 0 < a - b by linarith), sq_pos_of_pos (show 0 < 1 - a by linarith), sq_pos_of_pos (show 0 < 1 - b by linarith)]
  
  have h2 : x < (1 - b) * (1 + a) := by
    rw [hx]
    nlinarith
  
  exact ⟨h1, h2⟩