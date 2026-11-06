import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_116599 {f : ℝ → ℝ} (h : ∀ x, cos (17 * x) = f (cos x)) :
    ∀ x, sin (17 * x) = f (sin x) := by
  intro x
  have h1 := h (Real.pi / 2 - x)
  have h2 : cos (17 * (Real.pi / 2 - x)) = f (cos (Real.pi / 2 - x)) := by
    simpa using h1
  have h3 : cos (17 * (Real.pi / 2 - x)) = sin (17 * x) := by
    have h4 : 17 * (Real.pi / 2 - x) = (17 * Real.pi / 2) - 17 * x := by
      ring
    rw [h4]
    have h5 : cos (17 * Real.pi / 2 - 17 * x) = cos (Real.pi / 2 - 17 * x) := by
      have h5 : Real.pi / 2 - 17 * x = (17 * Real.pi / 2 - 17 * x) - 8 * Real.pi := by
        ring_nf
      rw [h5]
      have h6 : cos ((17 * Real.pi / 2 - 17 * x) - 8 * Real.pi) = cos (17 * Real.pi / 2 - 17 * x) := by
        have h7 : cos ((17 * Real.pi / 2 - 17 * x) - 8 * Real.pi) = cos (17 * Real.pi / 2 - 17 * x) := by
          have h8 : (17 * Real.pi / 2 - 17 * x) - 8 * Real.pi = (17 * Real.pi / 2 - 17 * x) - 4 * (2 * Real.pi) := by
            ring
          rw [h8]
          have h9 : cos ((17 * Real.pi / 2 - 17 * x) - 4 * (2 * Real.pi)) = cos (17 * Real.pi / 2 - 17 * x) := by
            have h10 : cos ((17 * Real.pi / 2 - 17 * x) - 4 * (2 * Real.pi)) = cos (17 * Real.pi / 2 - 17 * x) := by
              have h11 : (17 * Real.pi / 2 - 17 * x) - 4 * (2 * Real.pi) = (17 * Real.pi / 2 - 17 * x) - (4 * (2 * Real.pi)) := by
                ring
              rw [h11]
              have h12 : cos ((17 * Real.pi / 2 - 17 * x) - (4 * (2 * Real.pi))) = cos (17 * Real.pi / 2 - 17 * x) := by
                have h13 : cos ((17 * Real.pi / 2 - 17 * x) - (4 * (2 * Real.pi))) = cos (17 * Real.pi / 2 - 17 * x) := by
                  have h14 : (17 * Real.pi / 2 - 17 * x) - (4 * (2 * Real.pi)) = (17 * Real.pi / 2 - 17 * x) - (2 * Real.pi) - (2 * Real.pi) - (2 * Real.pi) - (2 * Real.pi) := by
                    ring
                  rw [h14]
                  have h15 : cos ((17 * Real.pi / 2 - 17 * x) - (2 * Real.pi) - (2 * Real.pi) - (2 * Real.pi) - (2 * Real.pi)) = cos (17 * Real.pi / 2 - 17 * x) := by
                    rw [cos_sub_two_pi, cos_sub_two_pi, cos_sub_two_pi, cos_sub_two_pi]
                  linarith
                linarith
              linarith
            linarith
          linarith
        linarith
      linarith
    have h8 : cos (Real.pi / 2 - 17 * x) = sin (17 * x) := by 
      have h9 : cos (Real.pi / 2 - 17 * x) = sin (17 * x) := by
        rw [cos_pi_div_two_sub]
      linarith
    rw [h5]
    linarith
  have h6 : cos (Real.pi / 2 - x) = sin x := by
    rw [cos_pi_div_two_sub]
  rw [h6] at h2
  linarith [h3, h2]