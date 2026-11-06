import Mathlib

theorem algebra_20067 {x : ℝ} (hx : x > 2.74 ∧ x < 2.75) :
    round (x * 10) = 27 := by 
  rcases hx with ⟨hx1, hx2⟩
  have h1 : x * 10 > 27.4 := by 
    nlinarith
  have h2 : x * 10 < 27.5 := by 
    nlinarith
  rw [round_eq]
  rw [Int.floor_eq_iff]
  constructor <;> (try norm_num) <;> linarith