import Mathlib

theorem algebra_2213 {x : ℝ} (hx : x ∈ Set.Ioo 0 π) (h : (π - x) / 2 = 2 * (π / 2 - x) - 3 * (π / 180)) :
    x = 58 * π / 180 := by
  rcases hx with ⟨hx1, hx2⟩
  linarith [h, Real.pi_pos, Real.pi_gt_three]