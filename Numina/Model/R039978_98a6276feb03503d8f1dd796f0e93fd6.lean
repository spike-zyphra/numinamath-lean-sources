import Mathlib

theorem number_theory_40803 (a : ℕ → ℕ) (ha : ∀ n, 0 < a n)
    (h : ∀ n, (n ^ 2 + 1) * a n = n * (a (n ^ 2) + 1)) :
    ∀ n, a n = n := by

  have h1 := h 0

  have h2 : (0 ^ 2 + 1) * a 0 = 0 * (a (0 ^ 2) + 1) := by
    simpa using h1

  have h3 : a 0 = 0 := by 
    omega

  have h4 : 0 < a 0 := by 
    apply ha 0

  omega -- contradiction