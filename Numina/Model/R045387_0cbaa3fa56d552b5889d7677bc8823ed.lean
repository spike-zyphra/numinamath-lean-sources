import Mathlib

open Real

theorem algebra_20182 {f : ℝ → ℝ} (hf : f = fun x => (4 * x + 1) / 3) :
    (f ⁻¹' {1})⁻¹ = {2} := by
  have h1 : ∀ x : ℝ, f x = 1 ↔ x = 1 / 2 := by
    intro x
    rw [hf]
    simp
    constructor
    · -- If f(x) = 1 then x = 1/2
      intro h
      linarith
    · -- If x = 1/2 then f(x) = 1
      intro h
      rw [h]
      norm_num
  have h2 : f ⁻¹' {1} = {1 / 2} := by
    ext x
    simp [h1]
  rw [h2]
  ext y
  simp
  <;> norm_num
  <;> tauto