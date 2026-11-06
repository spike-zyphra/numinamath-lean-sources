import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_279040 {f : ℝ → ℝ}
  (h : ∀ x, f x = x * cos (π / 2) - x * sin (π / 2)) :
  ∃! x, f x = x := by

  have h1 : cos (π / 2) = 0 := by
    have h2 : cos (π / 2) = 0 := by
      rw [cos_pi_div_two]
    exact h2
  have h2' : sin (π / 2) = 1 := by
    have h3 : sin (π / 2) = 1 := by
      rw [sin_pi_div_two]
    exact h3
  have hfx : ∀ x, f x = -x := by
    intro x
    rw [h x]
    simp [h1, h2']
    <;> ring
  use 0
  constructor
  · -- Show that 0 is a solution.
    norm_num [hfx]
  · -- Show that it's unique
    intro y hy
    have h_eq : f y = -y := hfx y
    rw [h_eq] at hy
    linarith