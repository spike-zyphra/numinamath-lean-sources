import Mathlib

theorem algebra_310196 (a : ℕ → ℕ) (ha : ∀ n, 0 < a n)
    (h1 : ∀ n, a n + a (n + 1) = 2007) (h2 : ∀ n, 31 * (a n ^ 2 + a n * a (n + 1) + a (n + 1) ^ 2) = 1345368366) :
    ∑ i in Finset.range 2007, a i = 1345368366 := by 
  have h3 := h2 0
  omega