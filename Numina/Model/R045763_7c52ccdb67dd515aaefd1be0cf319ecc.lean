import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_146706 {f : ℝ → ℝ}
  (h : ∀ x ∈ Icc 0 Real.pi, f (cos x) = x / 2) :
  f (-1 / 2) = Real.pi / 3 := by
  have h2pi3 : f (cos (2 * Real.pi / 3)) = (2 * Real.pi / 3) / 2 := by
    specialize h (2 * Real.pi / 3) (by
      constructor
      · -- Show 0 ≤ 2π/3
        have hpi : Real.pi > 0 := Real.pi_pos
        nlinarith [Real.pi_pos]
      · -- Show 2π/3 ≤ π
        have hpi : Real.pi > 0 := Real.pi_pos
        nlinarith [Real.pi_pos]
    )
    simpa using h

  have hcos : cos (2 * Real.pi / 3) = -1 / 2 := by 
    have h1 : 2 * Real.pi / 3 = Real.pi - (Real.pi / 3) := by 
      linarith [Real.pi_pos]
    rw [h1]
    rw [cos_pi_sub]
    have h2 : cos (Real.pi / 3) = 1 / 2 := by 
      exact cos_pi_div_three
    linarith [h2]

  calc
    f (-1 / 2) = f (cos (2 * Real.pi / 3)) := by
      rw [hcos]
    _ = (2 * Real.pi / 3) / 2 := by 
      rw [h2pi3]
    _ = Real.pi / 3 := by 
      ring