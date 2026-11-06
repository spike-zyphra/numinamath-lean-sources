import Mathlib

theorem algebra_224280 {f : ℝ → ℝ} (h : ∀ x y, x ≠ 0 → y ≠ 0 → f x + f y = f x * f y + 1 - 4 / (x * y)) (h1 : f 1 > 0) :
    f 4 = 3 / 2 := by
  have h1_eq : f 1 = 3 := by
    have h11 := h 1 1 (by norm_num) (by norm_num)
    norm_num at h11
    have h1_eq : f 1 ^ 2 - 2 * f 1 - 3 = 0 := by linarith
    have h2 : (f 1 - 3) * (f 1 + 1) = 0 := by
      linarith [h1_eq]
    cases' (mul_eq_zero.mp h2) with h3 h4
    · -- Case $f(1) - 3 = 0$, so $f(1) = 3$.
      linarith
    · -- Case $f(1) + 1 = 0$, so $f(1) = -1$.
      have h5 : f 1 = -1 := by linarith
      linarith [h1, h5]
  have h14 := h 1 4 (by norm_num) (by norm_num)
  rw [h1_eq] at h14
  norm_num at h14
  linarith