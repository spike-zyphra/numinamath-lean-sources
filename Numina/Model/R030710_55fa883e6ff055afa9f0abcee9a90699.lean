import Mathlib

open Real

theorem algebra_147 : ∑ i ∈ Finset.range 2009, √(1 + (1 / (i + 1)^2:ℝ) + 1 / (i + 2)^2:ℝ) = 2009 * (2011 / 2010 : ℝ) := by
  have h1 : ∀ i : ℕ, √(1 + (1 / ((i : ℝ) + 1)^2) + (1 / ((i : ℝ) + 2)^2)) = 1 + (1 / ((i + 1 : ℝ) * ((i + 2 : ℝ)))) := by
    intro i
    have h2 : (1 : ℝ) + (1 / ((i + 1 : ℝ) ^ 2)) + (1 / ((i + 2 : ℝ) ^ 2)) = (1 + (1 / ((i + 1 : ℝ) * ((i + 2 : ℝ)) ) ) ) ^ 2 := by
      field_simp
      ring
    rw [h2]
    have h3 : 0 ≤ (1 + (1 / ((i + 1 : ℝ) * ((i + 2 : ℝ)) ) ) : ℝ) := by positivity
    rw [Real.sqrt_sq (h3)]
  rw [Finset.sum_congr rfl (fun i _ => h1 i)]
  norm_num
  <;> native_decide