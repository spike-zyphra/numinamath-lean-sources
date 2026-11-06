import Mathlib

theorem algebra_162634 (p : ℝ) (h₀ : p ≥ 0) (h₁ : ∃ r, 2 * Real.sqrt p = r * (p - 2) ∧ -3 - p = r * 2 * Real.sqrt p) :
    p = 1 := by
  rcases h₁ with ⟨r, h2, h3⟩
  by_cases hp2 : p - 2 = 0
  · -- Case where p - 2 = 0, so p = 2
    have hp : p = 2 := by linarith
    rw [hp] at h2
    have h4 : Real.sqrt (2 : ℝ) > 0 := Real.sqrt_pos.mpr (by norm_num)
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  · -- Case where p - 2 ≠ 0
    have h4 : (p - 2) ≠ 0 := by intro h; apply hp2; linarith
    have hr : r = (2 * Real.sqrt p) / (p - 2) := by
      field_simp [h4]
      linarith
    rw [hr] at h3
    have eq1 : (p - 2) * (-3 - p) = 4 * p := by
      have h5 : (p - 2) ≠ 0 := h4
      field_simp [h5] at h3
      nlinarith [Real.sqrt_nonneg p, Real.sq_sqrt (show 0 ≤ p by linarith)]
    have h5 : p ^ 2 + 5 * p - 6 = 0 := by
      nlinarith [eq1]
    have h6 : (p - 1) * (p + 6) = 0 := by
      nlinarith [h5]
    cases' (mul_eq_zero.mp h6) with hp1 hp6
    · -- Case where p - 1 = 0, so p = 1
      linarith
    · -- Case where p + 6 = 0, so p = -6
      have hp6' : p = -6 := by linarith
      nlinarith [h₀, hp6']