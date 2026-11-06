import Mathlib

theorem other_99815 (x : ℝ) (hx : x ∈ Set.Icc 0 100) (h : (100 - x) * 90 / 100 + x * 100 / 100 = 46 * 100) :
    x = 40 := by 
  rcases hx with ⟨hx1, hx2⟩
  nlinarith