import Mathlib

theorem algebra_114917 (x : ℝ) (hx : x ∈ Set.Icc 0 9) (h : (91 * 7 + x) / 8 = 91) :
    (91 * 7 + x) ^ 2 / 8 - 91 ^ 2 = 36 / 7 := by
  rcases hx with ⟨hx0, hx1⟩
  linarith -- This will reveal a contradiction in the problem constraints