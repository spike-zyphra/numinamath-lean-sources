import Mathlib

theorem algebra_230716 (x : ℝ) (hx : x ∈ Set.Ioo 0 1) (h : 20 * x + 60 * (1 - x) = 52) :
    x = 1 / 5 := by
  rcases hx with ⟨hx1, hx2⟩ -- x ∈ (0,1), so 0 < x < 1
  linarith