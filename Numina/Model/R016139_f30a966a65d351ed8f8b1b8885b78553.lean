import Mathlib

open Real Set
open scoped Real

theorem algebra_253612 (x : ℝ) (h : cos (x / 2) = cos (x / 3)) :
    x ∉ Ioo 0 π := by
  by_contra h'
  rcases h' with ⟨hx1, hx2⟩
  have h3 : x / 2 > 0 := by linarith
  have h4 : x / 3 > 0 := by linarith
  have h5 : x / 2 < Real.pi := by
    linarith [Real.pi_gt_three]
  have h6 : x / 3 < Real.pi := by
    linarith [Real.pi_gt_three]
  have h7 : x / 2 = x / 3 := by
    have h8 : cos (x / 2) = cos (x / 3) := h
    have h9 : x / 2 ≥ 0 := by linarith
    have h10 : x / 3 ≥ 0 := by linarith
    have h11 : x / 2 ≤ Real.pi := by
      nlinarith [Real.pi_gt_three, hx2]
    have h12 : x / 3 ≤ Real.pi := by
      nlinarith [Real.pi_gt_three, hx2]
    have h13 : x / 2 = x / 3 := by
      apply Real.injOn_cos
      · -- Show that x/2 ∈ [0, π]
        exact ⟨by linarith, by nlinarith [Real.pi_gt_three, hx2]⟩
      · -- Show that x/3 ∈ [0, π]
        exact ⟨by linarith, by nlinarith [Real.pi_gt_three, hx2]⟩
      · -- The equality cos(a) = cos(b)
        exact h8
    exact h13
  -- From h7, we get x / 2 = x / 3 implies x = 0
  have h8 : x = 0 := by
    linarith [h7]
  -- This contradicts with x > 0
  linarith [h8, hx1]