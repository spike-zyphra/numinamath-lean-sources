import Mathlib

open Real

theorem algebra_300869 :
    ⌊∑ i ∈ Finset.range 1999, sqrt (1 + 1 / (i + 1)^2 + 1 / (i + 2)^2)⌋ = 1999 := by

  have h1 : ∀ i : ℕ, sqrt (1 + 1 / (i + 1)^2 + 1 / (i + 2)^2) = 1 + 1 / ((i + 1) * (i + 2)) := by
    intro i
    have h2 : (1 + 1 / (i + 1)^2 + 1 / (i + 2)^2 : ℝ) = (1 + 1 / ((i + 1) * (i + 2)))^2 := by
      field_simp
      ring
    rw [h2]
    rw [Real.sqrt_sq (by positivity)]

  rw [Finset.sum_congr rfl (fun i _ => h1 i)]
  norm_num [Finset.sum_range_succ]
  <;> try { native_decide }