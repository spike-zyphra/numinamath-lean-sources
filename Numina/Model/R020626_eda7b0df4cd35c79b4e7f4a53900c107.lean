import Mathlib

open Real Set
open scoped Real

theorem algebra_212529 {f : ℝ → ℝ} (h : ∀ x, f (cos x) = cos (17 * x)) :
    ∀ x, f (sin x) = sin (17 * x) := by
  intro x 
  have h1 : sin x = cos (Real.pi / 2 - x) := by 
    rw [← cos_pi_div_two_sub]
  have h6 : f (sin x) = cos (17 * (Real.pi / 2 - x)) := by
    rw [h1]
    have h2 := h (Real.pi / 2 - x)
    simpa using h2
  have h3 : cos (17 * (Real.pi / 2 - x)) = cos (17 * Real.pi / 2 - 17 * x) := by
    ring_nf
  have h4 : cos (17 * Real.pi / 2 - 17 * x) = sin (17 * x) := by
    have h11 : 17 * Real.pi / 2 = 8 * Real.pi + Real.pi / 2 := by 
      linarith [Real.pi_pos]
    rw [h11]
    have h12 : cos ( (8 * Real.pi + Real.pi / 2 : ℝ) - 17 * x ) = cos ( Real.pi / 2 - 17 * x ) := by
      have h8 : (8 * Real.pi + Real.pi / 2 : ℝ) - 17 * x = (Real.pi / 2 - 17 * x ) + 4 * (2 * Real.pi) := by 
        nlinarith [Real.pi_pos]
      rw [h8]
      have h9 : cos ( (Real.pi / 2 - 17 * x ) + 4 * (2 * Real.pi) ) = cos (Real.pi / 2 - 17 * x ) := by
        have h10 : cos ( (Real.pi / 2 - 17 * x ) + 4 * (2 * Real.pi) ) = cos ( (Real.pi / 2 - 17 * x ) ) := by 
          have h11 : cos ( (Real.pi / 2 - 17 * x ) + 4 * (2 * Real.pi) ) = cos ( (Real.pi / 2 - 17 * x ) + (4 : ℕ) * (2 * Real.pi) ) := by 
            ring_nf
          rw [h11]
          have h12 : cos ( (Real.pi / 2 - 17 * x ) + (4 : ℕ) * (2 * Real.pi) ) = cos ( (Real.pi / 2 - 17 * x ) ) := by
            have h13 : cos ( (Real.pi / 2 - 17 * x ) + (4 : ℕ) * (2 * Real.pi) ) = cos ( (Real.pi / 2 - 17 * x ) ) := by 
              apply cos_add_nat_mul_two_pi
            exact_mod_cast h13
          exact_mod_cast h12
        exact_mod_cast h10
      exact_mod_cast h9
    have h13 : cos ( Real.pi / 2 - 17 * x ) = sin (17 * x ) := by
      have h21 : cos ( Real.pi / 2 - 17 * x ) = sin (17 * x ) := by
        have h23 : cos ( Real.pi / 2 - 17 * x ) = cos ( Real.pi / 2 ) * cos (17 * x ) + sin ( Real.pi / 2 ) * sin (17 * x ) := by
          rw [cos_sub]
        have h24 : cos (Real.pi / 2 ) = (0 : ℝ) := by
          rw [cos_pi_div_two]
        have h25 : sin (Real.pi / 2 ) = (1 : ℝ) := by
          rw [sin_pi_div_two]
        rw [h24, h25] at h23
        nlinarith
      exact_mod_cast h21
    rw [h12, h13]
  have h9 : f (sin x) = sin (17 * x) := by 
    rw [h6]
    rw [h3]
    exact_mod_cast h4
  exact_mod_cast h9