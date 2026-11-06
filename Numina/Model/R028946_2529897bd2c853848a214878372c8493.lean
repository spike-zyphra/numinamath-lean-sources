import Mathlib

theorem algebra_269872 {f : ℕ → ℕ → ℝ} (h1 : ∀ m n, 2 * f m n = 2 + f (m + 1) (n - 1) + f (m - 1) (n + 1))
    (h2 : ∀ m, f m 0 = 0) (h3 : ∀ n, f 0 n = 0) :
    ∀ m n, f m n = n := by

  have eq1 := h1 0 0
  have h4 : f 0 0 = 0 := h3 0
  have h5 : f 1 0 = 0 := h2 1
  have h6 : f 0 1 = 0 := h3 1
  norm_num [h4, h5, h6] at eq1 
  all_goals linarith