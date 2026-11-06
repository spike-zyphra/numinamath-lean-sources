import Mathlib

theorem calculus_74008 (α : ℝ) :
    Real.cos α + Real.cos (α + 2 * Real.pi / 3) + Real.cos (α + 4 * Real.pi / 3) =
    0 ∧
    Real.sin α + Real.sin (α + 2 * Real.pi / 3) + Real.sin (α + 4 * Real.pi / 3) =
    0 := by
  have hcos1 : Real.cos (α + 2 * Real.pi / 3) = Real.cos α * Real.cos (2 * Real.pi / 3) - Real.sin α * Real.sin (2 * Real.pi / 3) := by
    rw [Real.cos_add]
  have hcos2 : Real.cos (α + 4 * Real.pi / 3) = Real.cos α * Real.cos (4 * Real.pi / 3) - Real.sin α * Real.sin (4 * Real.pi / 3) := by
    rw [Real.cos_add]
  have h_cos2pi3 : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
    have h1 : Real.cos (2 * Real.pi / 3) = Real.cos (Real.pi - (Real.pi / 3)) := by
      ring
    rw [h1]
    rw [Real.cos_pi_sub]
    have : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
    linarith
  have h_sin2pi3 : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
    have h1 : Real.sin (2 * Real.pi / 3) = Real.sin (Real.pi - (Real.pi / 3)) := by
      ring
    rw [h1]
    rw [Real.sin_pi_sub]
    have : Real.sin (Real.pi / 3) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
    linarith
  have h_cos4pi3 : Real.cos (4 * Real.pi / 3) = -1 / 2 := by
    have h1 : Real.cos (4 * Real.pi / 3) = Real.cos (Real.pi + (Real.pi / 3)) := by
      ring
    rw [h1]
    rw [Real.cos_add, Real.cos_pi, Real.sin_pi]
    norm_num [Real.cos_pi_div_three, Real.sin_pi_div_three]
    all_goals
      ring_nf
      <;> norm_num [Real.cos_pi_div_three, Real.sin_pi_div_three]
  have h_sin4pi3 : Real.sin (4 * Real.pi / 3) = -Real.sqrt 3 / 2 := by
    have h1 : Real.sin (4 * Real.pi / 3) = Real.sin (Real.pi + (Real.pi / 3)) := by
      ring
    rw [h1]
    rw [Real.sin_add, Real.sin_pi, Real.cos_pi]
    norm_num [Real.sin_pi_div_three, Real.cos_pi_div_three]
    all_goals
      ring_nf
      <;> norm_num [Real.sin_pi_div_three, Real.cos_pi_div_three]
  have hcos : Real.cos α + Real.cos (α + 2 * Real.pi / 3) + Real.cos (α + 4 * Real.pi / 3) = 0 := by 
    rw [hcos1, hcos2]
    rw [h_cos2pi3, h_sin2pi3, h_cos4pi3, h_sin4pi3]
    ring_nf
  have hsin1 : Real.sin (α + 2 * Real.pi / 3) = Real.sin α * Real.cos (2 * Real.pi / 3) + Real.cos α * Real.sin (2 * Real.pi / 3) := by
    rw [Real.sin_add]
  have hsin2 : Real.sin (α + 4 * Real.pi / 3) = Real.sin α * Real.cos (4 * Real.pi / 3) + Real.cos α * Real.sin (4 * Real.pi / 3) := by
    rw [Real.sin_add]
  have hsin : Real.sin α + Real.sin (α + 2 * Real.pi / 3) + Real.sin (α + 4 * Real.pi / 3) = 0 := by 
    rw [hsin1, hsin2]
    rw [h_cos2pi3, h_sin2pi3, h_cos4pi3, h_sin4pi3]
    ring_nf
  constructor
  · exact hcos
  · exact hsin