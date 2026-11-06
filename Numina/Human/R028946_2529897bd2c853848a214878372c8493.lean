import Mathlib

/-Find a function f(m,n) that satisfies the following conditions: for every pair of non-negative integers m,n
(1)2 * f m n = 2 + f (m + 1) (n - 1) + f (m - 1) (n + 1)
(2)f m 0 = f 0 n = 0-/
theorem algebra_269872 {f : ℕ → ℕ → ℝ} (h1 : ∀ m n, 2 * f m n = 2 + f (m + 1) (n - 1) + f (m - 1) (n + 1))
    (h2 : ∀ m, f m 0 = 0) (h3 : ∀ n, f 0 n = 0) :
    ∀ m n, f m n = n := by 
  intro m n
  have h1' := h1 0 0
  simp [h2, h3] at h1'