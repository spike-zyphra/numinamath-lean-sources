import Mathlib

theorem algebra_320283 {k : ℝ} (y₁ y₂ : ℝ) (h₁ : 4 * y₁^2 + 4 * (2 - k) * y₁ - k^2 = 0)
    (h₂ : 4 * y₂^2 + 4 * (2 - k) * y₂ - k^2 = 0) (h₃ : |y₁| = 2 + |y₂|) :
    k = 0 ∨ k = 4 := by
  cases' abs_cases y₁ with h1 h1 <;> cases' abs_cases y₂ with h2 h2
  · -- Case y₁ ≥ 0, y₂ ≥ 0
    have h4 : y₁ = 2 + y₂ := by
      rw [abs_of_nonneg h1.2, abs_of_nonneg h2.2] at h₃
      linarith
    have h5 : (y₁ - y₂) * (y₁ + y₂ + 2 - k) = 0 := by
      nlinarith
    have h6 : (y₁ - y₂) ≠ 0 := by
      by_contra h7
      have : y₁ = y₂ := by linarith
      nlinarith [h₃, h4, sq_nonneg (y₁ - y₂)]
    have hk1 : k = y₁ + y₂ + 2 := by
      apply (mul_left_inj' (show (y₁ - y₂) ≠ 0 by exact h6)).mp
      linarith [h5]
    rw [show k = y₁ + y₂ + 2 by linarith [hk1]] at h₁ h₂
    nlinarith [sq_nonneg (y₂), sq_nonneg (y₁ - (2 + y₂)), sq_nonneg (k - 4), sq_nonneg (k), sq_nonneg (y₁ - y₂)]
  · -- Case y₁ ≥ 0, y₂ < 0
    have h4 : y₁ = 2 - y₂ := by
      rw [abs_of_nonneg h1.2, abs_of_neg h2.2] at h₃
      linarith
    have h5 : (y₁ - y₂) * (y₁ + y₂ + 2 - k) = 0 := by
      nlinarith
    have h6 : (y₁ - y₂) ≠ 0 := by
      by_contra h7
      have : y₁ = y₂ := by linarith
      nlinarith [h₃, h4, sq_nonneg (y₁ - y₂)]
    have hk1 : k = y₁ + y₂ + 2 := by
      apply (mul_left_inj' (show (y₁ - y₂) ≠ 0 by exact h6)).mp
      linarith [h5]
    have h8 : k = 4 := by
      nlinarith [sq_nonneg (y₂), sq_nonneg (y₁ - (2 - y₂)), sq_nonneg (k - 4), sq_nonneg (y₁ - y₂)]
    right
    linarith
  · -- Case y₁ < 0, y₂ ≥ 0
    have h4 : -y₁ = 2 + y₂ := by
      rw [abs_of_neg h1.2, abs_of_nonneg h2.2] at h₃
      linarith
    have h5 : (y₁ - y₂) * (y₁ + y₂ + 2 - k) = 0 := by
      nlinarith
    have h6 : (y₁ - y₂) ≠ 0 := by
      by_contra h7
      have : y₁ = y₂ := by linarith
      nlinarith [h₃, h4, sq_nonneg (y₁ - y₂)]
    have hk1 : k = y₁ + y₂ + 2 := by
      apply (mul_left_inj' (show (y₁ - y₂) ≠ 0 by exact h6)).mp
      linarith [h5]
    have h8 : k = 0 := by
      nlinarith [sq_nonneg (y₂), sq_nonneg (y₁ + y₂), sq_nonneg (y₁ - y₂), sq_nonneg (k - 0)]
    left
    linarith
  · -- Case y₁ < 0, y₂ < 0
    have h4 : -y₁ = 2 - y₂ := by
      rw [abs_of_neg h1.2, abs_of_neg h2.2] at h₃
      linarith
    have h5 : (y₁ - y₂) * (y₁ + y₂ + 2 - k) = 0 := by
      nlinarith
    have h6 : (y₁ - y₂) ≠ 0 := by
      by_contra h7
      have : y₁ = y₂ := by linarith
      nlinarith [h₃, h4, sq_nonneg (y₁ - y₂)]
    have hk1 : k = y₁ + y₂ + 2 := by
      apply (mul_left_inj' (show (y₁ - y₂) ≠ 0 by exact h6)).mp
      linarith [h5]
    -- Substitute k = y₁ + y₂ + 2 into the first equation
    rw [show k = y₁ + y₂ + 2 by linarith [hk1]] at h₁ h₂
    have hk2 : k = 0 ∨ k = 4 := by
      have h6 : (y₁ - y₂) * (y₁ + y₂ + 2 - k) = 0 := by
        nlinarith
      -- This equation is automatically satisfied as k = y1 + y2 + 2
      -- We need to solve the system after substituting k.
      have h8 : (k - 0) * (k - 4) = 0 := by
        nlinarith [sq_nonneg (y₂ - 1), sq_nonneg (y₁ - (-1)), sq_nonneg (y₁ - y₂), sq_nonneg (k)]
      cases' (mul_eq_zero.1 h8) with h9 h10
      · -- k - 0 = 0
        left
        linarith
      · -- k - 4 = 0
        right
        linarith
    tauto