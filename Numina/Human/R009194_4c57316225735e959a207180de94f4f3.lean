import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_146493 {f : ℝ → ℝ} (hf : f = λ x => sin x / (1 + cos x)) :
    f (π / 3) * f (2 * π / 3) = 1 := by
  rw [hf]
  have h1 : sin (π / 3) = sqrt 3 / 2 := by
    exact sin_pi_div_three
  have h2 : cos (π / 3) = 1 / 2 := by
    exact cos_pi_div_three
  have h3 : sin (2 * π / 3) = sqrt 3 / 2 := by
    have : 2 * π / 3 = π - π / 3 := by ring
    rw [this]
    rw [sin_pi_sub]
    exact sin_pi_div_three
  have h4 : cos (2 * π / 3) = -1 / 2 := by
    have : 2 * π / 3 = π - π / 3 := by ring
    rw [this]
    rw [cos_pi_sub]
    norm_num [cos_pi_div_three]
  simp [h1, h2, h3, h4]
  ring_nf
  norm_num