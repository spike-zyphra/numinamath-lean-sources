import Mathlib

theorem algebra_2292 {x : ℝ} (hx : x ∈ Set.Ioo 0 90) : x = 2 * (90 - x) ↔ x = 60 := by 
  rcases hx with ⟨hx1, hx2⟩
  constructor
  · -- Forward direction: Assume x = 2*(90 - x), prove x = 60
    intro h
    linarith
  · -- Backward direction: Assume x = 60, prove x = 2*(90 - x)
    intro h
    rw [h]
    norm_num