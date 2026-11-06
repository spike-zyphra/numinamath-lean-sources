import Mathlib

open Real

theorem algebra_311568 : ∑ i ∈ Finset.range 99, sqrt ((i + 1)^4 + (i + 2)^4 + 1) / ((i + 1)^2 + (i + 2)^2 - 1) = 9999 * sqrt 2 / 200 := by
  have h1 : ∀ i : ℕ, sqrt ((i + 1 : ℝ)^4 + (i + 2)^4 + 1) = Real.sqrt (2) * ((i + 1 : ℝ)^2 + (i + 1) + 1) := by
    intro i
    have h2 : ((i + 1 : ℝ) ^ 4 + (i + 2 : ℝ) ^ 4 + 1 : ℝ) = 2 * ((i + 1 : ℝ) ^ 2 + (i + 1) + 1) ^ 2 := by
      ring_nf
    rw [h2]
    have h3 : Real.sqrt (2 * ((i + 1 : ℝ) ^ 2 + (i + 1) + 1) ^ 2) = Real.sqrt (2 : ℝ) * ((i + 1 : ℝ) ^ 2 + (i + 1) + 1) := by
      have h4 : Real.sqrt (2 * ((i + 1 : ℝ) ^ 2 + (i + 1) + 1) ^ 2) = Real.sqrt (2 : ℝ) * Real.sqrt (((i + 1 : ℝ) ^ 2 + (i + 1) + 1) ^ 2) := by
        rw [Real.sqrt_mul (by positivity)]
      rw [h4]
      have h5 : Real.sqrt (((i + 1 : ℝ) ^ 2 + (i + 1) + 1) ^ 2) = ((i + 1 : ℝ) ^ 2 + (i + 1) + 1) := by
        rw [Real.sqrt_sq (by positivity)]
      rw [h5]
    linarith
  have h2 : ∀ i : ℕ, sqrt ((i + 1 : ℝ)^4 + (i + 2)^4 + 1) / ((i + 1)^2 + (i + 2)^2 - 1) = Real.sqrt (2) / (2 : ℝ) * (1 + 1 / (((i + 1) : ℝ) * ((i + 2) : ℝ))) := by
    intro i
    have h4 : sqrt ((i + 1 : ℝ)^4 + (i + 2)^4 + 1) = Real.sqrt (2 : ℝ) * ((i + 1 : ℝ) ^ 2 + (i + 1) + 1) := h1 i
    have h5 : ((i + 1 : ℝ) ^ 2 + (i + 2 : ℝ) ^ 2 - 1) = 2 * ((i + 1 : ℝ) * ((i + 2) : ℝ)) := by
      ring_nf
    rw [h4, h5]
    field_simp
    ring_nf
  have h3 : ∑ i in Finset.range 99, sqrt ((i + 1)^4 + (i + 2)^4 + 1) / ((i + 1)^2 + (i + 2)^2 - 1) = 
          ∑ i in Finset.range 99, (Real.sqrt (2) / (2 : ℝ) * (1 + 1 / (((i + 1) : ℝ) * ((i + 2) : ℝ)))) := by
    apply Finset.sum_congr
    · rfl
    · intro i hi
      exact h2 i
  rw [h3]
  have h4 : ∑ i in Finset.range 99, (Real.sqrt (2) / (2 : ℝ) * (1 + 1 / (((i + 1) : ℝ) * ((i + 2) : ℝ)))) = Real.sqrt (2) / (2 : ℝ) * (∑ i in Finset.range 99, (1 + 1 / (((i + 1) : ℝ) * ((i + 2) : ℝ)))) := by 
    rw [Finset.mul_sum]
  rw [h4]
  have h5 : ∑ i in Finset.range 99, (1 + 1 / (((i + 1) : ℝ) * ((i + 2) : ℝ))) = (99 + 99 / (100 : ℝ)) := by
    norm_num [Finset.sum_range_succ]
  rw [h5]
  field_simp
  <;> ring_nf <;> norm_num