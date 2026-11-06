import Mathlib

open Real Set
open scoped Real

theorem inequalities_603247 (a : ℝ) (h : ∀ θ ∈ Icc 0 (π/2), sqrt 2 * (2*a + 3) * cos (θ - π/4) +
    6 / (sin θ + cos θ) - 2 * sin (2*θ) < 3*a + 6) :
    a > 3 := by 
  have h1 := h (Real.pi / 2) (by
    constructor
    · -- Show that 0 ≤ π / 2
      linarith [Real.pi_pos]
    · -- Show that π / 2 ≤ π / 2
      linarith [Real.pi_pos]
  )
  have h2 : sqrt 2 * (2*a + 3) * cos (Real.pi / 2 - Real.pi / 4) + 6 / (sin (Real.pi / 2) + cos (Real.pi / 2)) - 2 * sin (2 * (Real.pi / 2)) < 3*a + 6 := by 
    linarith [h1]

  have eq1 : cos (Real.pi / 2 - Real.pi / 4) = Real.sqrt 2 / 2 := by
    have h2 : Real.pi / 2 - Real.pi / 4 = Real.pi / 4 := by ring
    rw [h2]
    rw [Real.cos_pi_div_four]

  have eq2 : sin (Real.pi / 2) = 1 := Real.sin_pi_div_two

  have eq3 : cos (Real.pi / 2) = 0 := Real.cos_pi_div_two

  have eq4 : sin (2 * (Real.pi / 2)) = 0 := by
    have h3 : 2 * (Real.pi / 2) = Real.pi := by ring
    rw [h3]
    rw [Real.sin_pi]

  rw [eq1, eq2, eq3, eq4] at h2
  nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)]