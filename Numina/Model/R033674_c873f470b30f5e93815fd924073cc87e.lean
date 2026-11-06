import Mathlib

theorem algebra_162662 {f : ℕ → ℕ → ℕ}
    (h1 : ∀ m n, 2 * f m n = 2 + f (m + 1) (n - 1) + f (m - 1) (n + 1))
    (h2 : ∀ m, f m 0 = 0) (h3 : ∀ n, f 0 n = 0) :
    ∀ m n, f m n = n := by
  have h4 := h1 0 0
  have eq1 : f 0 0 = 0 := by
    specialize h3 0
    simpa using h3
  have eq2 : f 1 0 = 0 := by
    specialize h2 1
    simpa using h2
  have eq3 : f 0 1 = 0 := by
    specialize h3 1
    simpa using h3
  simp [eq1, eq2, eq3] at h4
  all_goals omega