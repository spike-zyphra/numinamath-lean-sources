import Mathlib

open Real

theorem inequalities_116391 : ∑ i ∈ Finset.range 4028, sqrt ((i + 1) * (i + 2) / (2 * i + 3)^2) ≤ 2014 := by
  have h1 : ∀ i : ℕ, sqrt (((i + 1 : ℝ) * (i + 2 : ℝ) / (2 * i + 3 : ℝ)^2)) ≤ (1 : ℝ) / 2 := by
    intro i
    have h2 : ((i + 1 : ℝ) * (i + 2 : ℝ) / (2 * i + 3 : ℝ)^2) ≥ 0 := by positivity
    have h3 : sqrt (((i + 1 : ℝ) * (i + 2 : ℝ) / (2 * i + 3 : ℝ)^2)) ≤ (1 : ℝ) / 2 := by
      have h4 : sqrt (((i + 1 : ℝ) * (i + 2 : ℝ) / (2 * i + 3 : ℝ)^2)) ≥ 0 := by positivity
      have h5 : sqrt (((i + 1 : ℝ) * (i + 2 : ℝ) / (2 * i + 3 : ℝ)^2)) ^ 2 ≤ (1 : ℝ) / 4 := by
        have h6 : sqrt (((i + 1 : ℝ) * (i + 2 : ℝ) / (2 * i + 3 : ℝ)^2)) ^ 2 = ((i + 1 : ℝ) * (i + 2 : ℝ) / (2 * i + 3 : ℝ)^2) := Real.sq_sqrt (by positivity)
        rw [h6]
        have h7 : (2 * (i : ℝ) + 3) ^ 2 ≥ 0 := by positivity
        have h8 : (i + 1 : ℝ) * (i + 2 : ℝ) ≤ ( (2 * (i : ℝ) + 3) ^ 2 ) / 4 := by
          nlinarith [sq_nonneg ((i : ℝ) + 1 - 1 / 2)]
        have h9 : (i + 1 : ℝ) * (i + 2 : ℝ) / (2 * i + 3 : ℝ)^2 ≤ (1 : ℝ) / 4 := by
          apply (div_le_iff₀ (by positivity)).mpr
          nlinarith [h8]
        linarith [h9]
      nlinarith [Real.sqrt_nonneg (((i + 1 : ℝ) * (i + 2 : ℝ) / (2 * i + 3 : ℝ)^2)), h5]
    exact h3
  have h2 : ∑ i in Finset.range 4028, sqrt (((i + 1 : ℝ) * (i + 2 : ℝ) / (2 * i + 3 : ℝ)^2)) ≤ (2014 : ℝ) := by
    have h4 : ∑ i in Finset.range 4028, sqrt (((i + 1 : ℝ) * (i + 2 : ℝ) / (2 * i + 3 : ℝ)^2)) ≤ ∑ i in Finset.range 4028, ((1 : ℝ) / 2) := by
      apply Finset.sum_le_sum
      intro i hi
      specialize h1 i
      simpa using h1
    have h5 : ∑ i in Finset.range 4028, ((1 : ℝ) / 2) = (4028 : ℝ) * (1 / 2 : ℝ) := by
      simp [Finset.sum_const, Finset.card_range, mul_comm]
      <;> norm_num
    rw [h5] at h4
    norm_num at h4 ⊢
    linarith
  norm_num at h2 ⊢
  exact_mod_cast h2