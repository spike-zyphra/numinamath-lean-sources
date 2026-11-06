import Mathlib

open Real

theorem algebra_20261 (r R : ℝ) (hr : r > 0) (hR : R > 0)
    (hR1 : R = r / 2) :
    (π * R ^ 2) / (π * r ^ 2) = 25 / 100 := by

  have h1 : π * r ^ 2 ≠ 0 := by
    positivity

  have h2 : π * R ^ 2 = π * r ^ 2 / 4 := by
    rw [hR1]
    ring_nf
    <;> nlinarith [Real.pi_pos]

  have h3 : (π * R ^ 2) / (π * r ^ 2) = (π * R ^ 2) / (π * r ^ 2) := by rfl

  rw [h2]

  field_simp [h1]
  <;> nlinarith [Real.pi_pos]