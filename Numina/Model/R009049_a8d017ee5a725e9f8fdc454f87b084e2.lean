import Mathlib
theorem algebra_21116 {f : ℝ → ℝ} (hf : ∀ x, f x = x ^ 2 + 12) (m : ℝ) (hm : m > 0)
    (h : f (3 * m) = 3 * f m) : m = 2 := by
  have eq1 : f (3 * m) = (3 * m) ^ 2 + 12 := by
    apply hf
  have eq2 : f m = m ^ 2 + 12 := by
    apply hf
  rw [eq1, eq2] at h
  have eq3 : 6 * m ^ 2 = 24 := by
    nlinarith
  have eq4 : m ^ 2 = 4 := by
    nlinarith
  have h1 : m = 2 := by
    have h3 : m ^ 2 - 4 = 0 := by
      nlinarith
    have h4 : (m - 2) * (m + 2) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h4) with h5 h6
    · linarith
    · linarith
  exact h1