import Mathlib

open Real Set


theorem algebra_221490 (x : ℝ) :
  (cos (π/4 + x) - sin (π/4 + x)) / (cos (π/4 + x) + sin (π/4 + x)) =
  -tan x := by
  have h1 : cos (π / 4 + x) = Real.sqrt 2 / 2 * (cos x - sin x) := by
    rw [cos_add]
    have h2 : cos (π / 4) = Real.sqrt 2 / 2 := by
      rw [cos_pi_div_four]
    have h3 : sin (π / 4) = Real.sqrt 2 / 2 := by
      rw [sin_pi_div_four]
    simp [h2, h3]
    all_goals ring
  have h2 : sin (π / 4 + x) = Real.sqrt 2 / 2 * (cos x + sin x) := by
    rw [sin_add]
    have h3 : cos (π / 4) = Real.sqrt 2 / 2 := by
      rw [cos_pi_div_four]
    have h4 : sin (π / 4) = Real.sqrt 2 / 2 := by
      rw [sin_pi_div_four]
    simp [h3, h4]
    all_goals ring
  have h3 : cos (π / 4 + x) - sin (π / 4 + x) = -Real.sqrt 2 * sin x := by
    rw [h1, h2]
    ring_nf
  have h4 : cos (π / 4 + x) + sin (π / 4 + x) = Real.sqrt 2 * cos x := by
    rw [h1, h2]
    ring_nf
  rw [h3, h4]
  have htan : -tan x = - (sin x / cos x) := by
    rw [tan_eq_sin_div_cos]
  rw [htan]
  by_cases h6 : cos x = 0
  · -- cos x = 0
    rw [h6]
    simp [h6]
  · -- cos x ≠ 0
    have h7 : Real.sqrt 2 * cos x ≠ 0 := by
      have h8 : Real.sqrt 2 ≠ 0 := by
        positivity
      have h9 : cos x ≠ 0 := h6
      intro h
      have h10 : Real.sqrt 2 = 0 ∨ cos x = 0 := by
        simpa using h
      cases h10 with
      | inl h11 =>
        contradiction
      | inr h11 =>
        contradiction
    field_simp [h7, h6]
    <;> ring_nf <;> field_simp [h6]