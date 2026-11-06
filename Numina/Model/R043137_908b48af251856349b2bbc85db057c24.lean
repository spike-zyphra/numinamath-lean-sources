import Mathlib

open Real

theorem algebra_98995 : ∑ k : ℕ in Finset.Icc 1 2016, (k * sqrt (k + 1) + (k + 1) * sqrt k)⁻¹ = 1 - 1 / sqrt 2017 := by
  have h1 : ∀ (k : ℕ), k ≥ 1 → (k * sqrt (k + 1) + (k + 1) * sqrt k) = Real.sqrt k * Real.sqrt (k + 1) * (Real.sqrt k + Real.sqrt (k + 1)) := by
    intro k hk
    have hk₀ : (k : ℝ) ≥ 0 := by positivity
    have hk₁ : (k + 1 : ℝ) ≥ 0 := by positivity
    have hk₂ : (k : ℝ) ≥ 1 := by exact_mod_cast (show k ≥ 1 by linarith)
    calc
      (k * sqrt (k + 1) + (k + 1) * sqrt k : ℝ) = (k * sqrt (k + 1) + (k + 1) * sqrt k : ℝ) := rfl
      _ = Real.sqrt k ^ 2 * Real.sqrt (k + 1) + Real.sqrt (k + 1) ^ 2 * Real.sqrt k := by
        have h2 : Real.sqrt k ^ 2 = (k : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ (k : ℝ) by positivity)
        have h3 : Real.sqrt (k + 1) ^ 2 = (k + 1 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ (k + 1 : ℝ) by positivity)
        rw [h2, h3]
      _ = Real.sqrt k * Real.sqrt (k + 1) * (Real.sqrt k + Real.sqrt (k + 1)) := by
        nlinarith [Real.sqrt_nonneg (k : ℝ), Real.sqrt_nonneg (k + 1 : ℝ)]
  have h2 : ∀ (k : ℕ), k ≥ 1 → (k * sqrt (k + 1) + (k + 1) * sqrt k)⁻¹ = (1 / sqrt k - 1 / sqrt (k + 1) : ℝ) := by
    intro k hk
    have hk0 : k ≥ 1 := hk
    have hk4 : (k : ℝ) ≥ 1 := by exact_mod_cast (show k ≥ 1 by linarith)
    have hk10 : (k * sqrt (k + 1) + (k + 1) * sqrt k : ℝ) = Real.sqrt k * Real.sqrt (k + 1) * (Real.sqrt k + Real.sqrt (k + 1)) := h1 k hk0
    rw [hk10]
    have hk31 : Real.sqrt k > 0 := by
      apply Real.sqrt_pos.mpr
      have hk31 : (k : ℝ) > 0 := by exact_mod_cast (show k > 0 by omega)
      linarith
    have hk32 : Real.sqrt (k + 1 : ℝ) > 0 := by
      apply Real.sqrt_pos.mpr
      have hk34 : (k + 1 : ℝ) > 0 := by exact_mod_cast (show (k + 1 : ℕ) > 0 by omega)
      linarith
    field_simp [Real.sqrt_nonneg (k : ℝ), Real.sqrt_nonneg (k + 1 : ℝ), mul_pos hk31 hk32, Real.sq_sqrt (show (0 : ℝ) ≤ (k : ℝ) by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ (k + 1 : ℝ) by positivity)]
    <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (k : ℝ) by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ (k + 1 : ℝ) by positivity), Real.sqrt_nonneg (k : ℝ), Real.sqrt_nonneg (k + 1 : ℝ)]
  have h3 : ∀ (n : ℕ), ∑ k : ℕ in Finset.Icc 1 n, (k * sqrt (k + 1) + (k + 1) * sqrt k)⁻¹ = 1 - 1 / sqrt (n + 1 : ℝ) := by
    intro n
    induction n with
    | zero =>
      norm_num [Finset.sum_eq_zero]
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by linarith)]
      rw [ih]
      rw [h2 (n + 1) (by linarith)]
      field_simp [Real.sqrt_pos.mpr (show (0 : ℝ) < n + 1 by positivity), Real.sqrt_pos.mpr (show (0 : ℝ) < (n + 1 + 1 : ℝ) by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ (n + 1 : ℝ) by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ (n + 1 + 1 : ℝ) by positivity)]
      all_goals
        ring_nf
  specialize h3 2016
  norm_num at h3 ⊢
  linarith