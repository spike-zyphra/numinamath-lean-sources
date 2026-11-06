import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_204522 {f : ℝ → ℝ} (hf : f = λ x => cos x) :
    ∃ x, x ∈ Ioo 0 (π/2) ∧ ∫ y in (0)..x, f y = ∫ y in (x)..(π/2), f y := by
  use π / 6
  constructor
  · -- Show that π / 6 is in the open interval (0, π / 2)
    constructor
    · -- Show that 0 < π / 6
      have h1 : 0 < π := Real.pi_pos
      linarith [h1]
    · -- Show that π / 6 < π / 2
      have h1 : 0 < π := Real.pi_pos
      have h2 : π / 6 < π / 2 := by 
        linarith [Real.pi_pos, Real.pi_gt_three]
      linarith [h1, h2]
  · -- Show that the integral from 0 to π/6 equals the integral from π/6 to π/2
    rw [hf]
    have h_eq : ∫ y in (0)..(π / 6), (fun (y : ℝ) => cos y) y = ∫ y in (π / 6)..(π / 2), (fun (y : ℝ) => cos y) y := by
      simp [intervalIntegral.integral_const, sin_pi_div_six, sin_pi_div_two]
      <;> linarith
    exact h_eq