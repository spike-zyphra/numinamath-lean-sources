import Mathlib

open Real

theorem algebra_220160 : ∑ i ∈ Finset.range 2013, sqrt (1 + 1 / (i + 1)^2 + 1 / (i + 2)^2) = 2014 - 1 / 2014 := by
  have h1 : ∀ i : ℕ, sqrt (1 + 1 / (i + 1)^2 + 1 / (i + 2)^2) = 1 + 1 / ((i + 1) * (i + 2)) := by
    intro i
    have h2 : (1 + 1 / (i + 1)^2 + 1 / (i + 2)^2 : ℝ) = (1 + 1 / ((i + 1) * (i + 2)) : ℝ) ^ 2 := by
      field_simp
      ring
    rw [h2]
    have h3 : 0 ≤ (1 + 1 / ((i + 1) * (i + 2)) : ℝ) := by
      positivity
    rw [Real.sqrt_sq (h3)]
    <;> field_simp
    <;> ring
  rw [Finset.sum_congr rfl (fun i _ => h1 i)]
  norm_num
  <;> native_decide