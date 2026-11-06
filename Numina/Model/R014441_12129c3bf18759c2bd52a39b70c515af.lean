import Mathlib

theorem algebra_111587 {a b c : ℝ} (ha : a ≠ 0) (h : a * Real.cos x ^ 2 + b * Real.cos x + c = 0)
    (h' : a = 4 ∧ b = 2 ∧ c = -1) :
    4 * Real.cos (2 * x) ^ 2 + 2 * Real.cos (2 * x) - 1 = 0 := by
  rcases h' with ⟨ha', hb', hc'⟩
  have h₁ : 4 * Real.cos x ^ 2 + 2 * Real.cos x - 1 = 0 := by 
    rw [ha'] at h
    rw [hb'] at h
    rw [hc'] at h
    linarith
  have h2 : Real.cos (2 * x) = 2 * Real.cos x ^ 2 - 1 := by
    rw [Real.cos_two_mul]
    <;> nlinarith [Real.cos_sq_add_sin_sq x]
  nlinarith [sq_nonneg (Real.cos x), sq_nonneg (Real.cos (2 * x) - Real.cos x), sq_nonneg (Real.cos (2 * x) + 1), sq_nonneg (Real.cos x ^ 2), Real.cos_sq_add_sin_sq x, h₁, h2]