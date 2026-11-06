import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_269583 {f : ℝ → ℝ} (hf : f = λ x => 2 * sin (π / 6 - 2 * x)) :
    MonotoneOn f (Icc (π / 3) (5 * π / 6)) := by
  intro x hx y hy hxy
  have h1 : x ≥ π / 3 := by
    have h : x ∈ Icc (π / 3) (5 * π / 6) := hx
    simp at h ⊢
    linarith
  have h2 : y ≤ 5 * π / 6 := by
    have h : y ∈ Icc (π / 3) (5 * π / 6) := hy
    simp at h ⊢
    linarith
  have h3 : x ≤ y := by linarith
  have h9 : f x ≤ f y := by
    have h10 : f x = 2 * sin (π / 6 - 2 * x) := by
      rw [hf]
    have h11 : f y = 2 * sin (π / 6 - 2 * y) := by
      rw [hf]
    rw [h10, h11]
    have h12 : sin (π / 6 - 2 * x) ≤ sin (π / 6 - 2 * y) := by
      have h15 : sin (π / 6 - 2 * y) - sin (π / 6 - 2 * x) ≥ 0 := by
        have h16 : sin (π / 6 - 2 * y) - sin (π / 6 - 2 * x) = 2 * cos ((π / 6 - (x + y))) * sin ((x - y) ) := by
          have h18 : sin (π / 6 - 2 * y) - sin (π / 6 - 2 * x) =
            2 * cos (( (π / 6 - 2 * y) + (π / 6 - 2 * x) ) / 2 ) * sin ( ( (π / 6 - 2 * y) - (π / 6 - 2 * x) ) / 2 ) := by
            rw [sin_sub_sin]
            all_goals ring_nf
          have h19 : ( (π / 6 - 2 * y) + (π / 6 - 2 * x) ) / 2 = (π / 6 - (x + y)) := by
            linarith [Real.pi_pos]
          have h20 : ( (π / 6 - 2 * y) - (π / 6 - 2 * x) ) / 2 = (x - y) := by
            linarith [Real.pi_pos]
          rw [h19, h20] at h18
          linarith
        rw [h16]
        have h17 : sin (x - y) ≤ 0 := by
          have h18 : x - y ≤ 0 := by linarith
          have h19 : sin (x - y) ≤ 0 := by
            have : sin (x - y) ≤ 0 := by
              have h20 : x - y ≤ 0 := h18
              have h21 : sin (x - y) ≤ sin (0 : ℝ) := by
                apply Real.sin_le_sin_of_le_of_le_pi_div_two
                all_goals linarith
              have h22 : sin (0 : ℝ) = 0 := Real.sin_zero
              linarith [h21, h22]
            linarith
          linarith
        have h23 : cos ((π / 6 - (x + y))) ≤ 0 := by
          have h24 : π / 6 - (x + y) ≤ -π / 2 := by
            nlinarith [Real.pi_pos, h1, h2, h3]
          have h25 : π / 6 - (x + y) ≥ -3 * π / 2 := by
            nlinarith [Real.pi_pos, h1, h2, h3]
          have h29 : cos ((π / 6 - (x + y))) ≤ 0 := by
            have h30 : π / 6 - (x + y) + 2 * π ≥ π / 2 := by
              nlinarith [Real.pi_pos]
            have h31 : π / 6 - (x + y) + 2 * π ≤ 3 * π / 2 := by
              nlinarith [Real.pi_pos]
            have h32 : cos ((π / 6 - (x + y))) = cos ((π / 6 - (x + y)) + 2 * π) := by
              rw [cos_add_two_pi]
            have h33 : cos ((π / 6 - (x + y)) + 2 * π) ≤ 0 := by
              apply Real.cos_nonpos_of_pi_div_two_le_of_le
              all_goals nlinarith
            linarith [h33, h32]
          linarith
        nlinarith
      linarith
    nlinarith
  linarith