import Mathlib

theorem number_theory_8778 {f : ℕ → ℕ} (h1 : f 1 = 1) (h2 : ∀ n, f (f n) = n) (h3 : ∀ n, f (2 * n) = 2 * f n + 1) :
    f 2020 = 1051 := by 
  have h5 : f 0 = 2 * f 0 + 1 := by 
    specialize h3 0 
    simpa using h3
  omega