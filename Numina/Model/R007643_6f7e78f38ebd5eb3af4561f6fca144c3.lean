import Mathlib

open Real

theorem algebra_13491 (area : ℝ → ℝ) (harea : ∀ d, area d = π * (d / 2) ^ 2) :
    (area 12 - area 10) / area 10 = 0.44 := by
  have h1 : area 12 = π * (12 / 2) ^ 2 := harea 12
  have h2 : area 10 = π * (10 / 2) ^ 2 := harea 10
  rw [h1, h2]
  field_simp
  ring_nf