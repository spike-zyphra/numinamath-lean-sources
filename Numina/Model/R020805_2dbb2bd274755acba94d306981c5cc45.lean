import Mathlib

theorem algebra_314745 {f : ℕ → ℕ → ℕ} (h1 : f 1 1 = 1) (h2 : ∀ m n, f m (n + 1) = f m n + 2)
    (h3 : ∀ m, f m 1 = 2 * f (m - 1) 1) :
    f 1 n = 2 ^ (n - 1) + 1 ∧ f n 1 = 2 ^ (n - 1) + 1 ∧ f 2002 9 = 2 ^ 2001 + 16 := by

  have h4 : f 1 1 = 2 * f 0 1 := by
    specialize h3 1
    simpa using h3

  have h5 : f 1 1 = 1 := h1

  have h6 : f 0 1 = 0 := by 
    omega

  have h7 : 1 = 0 := by
    omega

  all_goals omega