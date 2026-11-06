import Mathlib

open Real Set
open scoped Real

theorem algebra_145960 {f : ℝ → ℝ} (hf : f = λ x => (sin x - sin x ^ 3) / cos x ^ 3) :
    ∀ x, cos x ≠ 0 → f x = tan x := by
  intro x hx
  rw [hf]
  have htan : tan x = sin x / cos x := by
    rw [tan_eq_sin_div_cos]
  simp only [htan]
  have h1 : cos x ≠ 0 := hx
  have h2 : cos x ^ 3 ≠ 0 := by
    apply pow_ne_zero 3
    exact h1
  have h3 : sin x ^ 2 + cos x ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq x
  have eq4 : sin x - sin x ^ 3 = sin x * cos x ^ 2 := by
    calc
      sin x - sin x ^ 3 = sin x * (1 - sin x ^ 2) := by
        ring_nf
      _ = sin x * (cos x ^ 2) := by
        have eq : 1 - sin x ^ 2 = cos x ^ 2 := by
          linarith [Real.sin_sq_add_cos_sq x]
        rw [eq]
      _ = sin x * cos x ^ 2 := by
        ring_nf
  have h4 : cos x ^ 3 = cos x ^ 2 * cos x := by
    ring_nf
  rw [eq4]
  rw [h4]
  have h5 : cos x ^ 2 ≠ 0 := by
    apply pow_ne_zero 2
    exact h1
  field_simp [h1, h5, h2]
  <;> ring_nf
  <;> field_simp [h1, h5, h2]
  <;> nlinarith