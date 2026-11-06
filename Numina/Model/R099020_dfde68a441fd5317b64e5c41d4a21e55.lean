import Mathlib

open Real Set
open scoped Real

theorem algebra_323187 {x : ℝ} (hx : x ∈ Ioo (-3 * π / 4) (π / 4)) (h : cos (π / 4 - x) = -3 / 5) :
    cos (2 * x) = -24 / 25 := by
  rcases hx with ⟨hx1, hx2⟩
  have h1 : cos (π / 4 - x) = -3 / 5 := h
  have h2 : -3 * π / 4 < x := hx1
  have h3 : x < π / 4 := hx2
  have h4 : 0 < π / 4 - x := by linarith [h3, Real.pi_pos]
  have h5 : π / 4 - x < π := by
    linarith [h2, Real.pi_pos]
  have h5_pos : sin (π / 4 - x) > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    all_goals linarith [h4, h5, Real.pi_pos]

  have h7 : 2 * x = Real.pi / 2 - 2 * (Real.pi / 4 - x) := by
    linarith [Real.pi_pos]

  calc
    cos (2 * x) = cos (Real.pi / 2 - 2 * (Real.pi / 4 - x)) := by rw [h7]
    _ = sin (2 * (Real.pi / 4 - x)) := by rw [cos_pi_div_two_sub]
    _ = 2 * sin (Real.pi / 4 - x) * cos (Real.pi / 4 - x) := by rw [sin_two_mul]
    _ = 2 * sin (Real.pi / 4 - x) * (-3 / 5) := by rw [h1]
    _ = 2 * (4 / 5) * (-3 / 5) := by 
      have h8 : sin (Real.pi / 4 - x) = 4 / 5 := by
        have h9 : sin (Real.pi / 4 - x) ^ 2 + cos (Real.pi / 4 - x) ^ 2 = 1 := by
          exact Real.sin_sq_add_cos_sq (Real.pi / 4 - x)
        rw [show cos (Real.pi / 4 - x) = -3 / 5 by linarith] at h9
        have h10 : sin (Real.pi / 4 - x) > 0 := h5_pos
        nlinarith [sq_nonneg (sin (Real.pi / 4 - x) - 4 / 5)]
      rw [h8]
      all_goals nlinarith [Real.pi_pos]
    _ = -24 / 25 := by nlinarith