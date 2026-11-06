import Mathlib

open Real

theorem algebra_10618 {a b : ℝ} (f : ℕ → ℝ → ℝ)
    (h₀ : ∀ x, f 1 x = a * x + b)
    (h₁ : ∀ n ≥ 1, ∀ x, f (n + 1) x = f 1 (f n x))
    (h₂ : ∀ x, f 7 x = 128 * x + 381) :
    a + b = 5 := by

  have f1 : ∀ x, f 1 x = a * x + b := h₀
  have f2 : ∀ x, f 2 x = a ^ 2 * x + b * (a + 1) := by
    intro x
    have h3 : f 2 x = f 1 (f 1 x) := by apply h₁ 1 (by linarith) x
    rw [h3, f1, f1]
    ring
  have f3 : ∀ x, f 3 x = a ^ 3 * x + b * (a ^ 2 + a + 1) := by
    intro x
    have h4 : f 3 x = f 1 (f 2 x) := by apply h₁ 2 (by linarith) x
    rw [h4, f1, f2]
    ring
  have f4 : ∀ x, f 4 x = a ^ 4 * x + b * (a ^ 3 + a ^ 2 + a + 1) := by
    intro x
    have h5 : f 4 x = f 1 (f 3 x) := by apply h₁ 3 (by linarith) x
    rw [h5, f1, f3]
    ring
  have f5 : ∀ x, f 5 x = a ^ 5 * x + b * (a ^ 4 + a ^ 3 + a ^ 2 + a + 1) := by
    intro x
    have h6 : f 5 x = f 1 (f 4 x) := by apply h₁ 4 (by linarith) x
    rw [h6, f1, f4]
    ring
  have f6 : ∀ x, f 6 x = a ^ 6 * x + b * (a ^ 5 + a ^ 4 + a ^ 3 + a ^ 2 + a + 1) := by
    intro x
    have h7 : f 6 x = f 1 (f 5 x) := by apply h₁ 5 (by linarith) x
    rw [h7, f1, f5]
    ring
  have f7 : ∀ x, f 7 x = a ^ 7 * x + b * (a ^ 6 + a ^ 5 + a ^ 4 + a ^ 3 + a ^ 2 + a + 1) := by
    intro x
    have h8 : f 7 x = f 1 (f 6 x) := by apply h₁ 6 (by linarith) x
    rw [h8, f1, f6]
    ring
  have eq1 := h₂ 0
  simp [f7] at eq1
  -- From h₂ 0, we get b * (a ^ 6 + a ^ 5 + a ^ 4 + a ^ 3 + a ^ 2 + a + 1) = 381
  have eq2 := h₂ 1
  simp [f7] at eq2
  -- From h₂ 1, we get a ^ 7 + b * (a ^ 6 + a ^ 5 + a ^ 4 + a ^ 3 + a ^ 2 + a + 1) = 509

  have eq3 : a ^ 7 = 128 := by
    nlinarith
  have eq4 : a = 2 := by
    have h3 : a ^ 7 - 128 = 0 := by linarith
    have h4 : a ^ 7 - 128 = (a - 2) * (a ^ 6 + 2 * a ^ 5 + 4 * a ^ 4 + 8 * a ^ 3 + 16 * a ^ 2 + 32 * a + 64) := by ring
    rw [h4] at h3
    cases' (mul_eq_zero.1 h3) with h5 h6
    · -- h5 : a - 2 = 0
      linarith
    · -- h6 : a ^ 6 + 2 * a ^ 5 + 4 * a ^ 4 + 8 * a ^ 3 + 16 * a ^ 2 + 32 * a + 64 = 0
      nlinarith [sq_nonneg (a ^ 3 + a ^ 2), sq_nonneg (a ^ 2 + 2), sq_nonneg (a + 2), sq_nonneg (a ^ 2 - 2*a + 2), sq_nonneg (a+1), sq_nonneg (a - 1)]
  have eq5 : b = 3 := by
    rw [eq4] at eq1
    nlinarith
  linarith [eq4, eq5]