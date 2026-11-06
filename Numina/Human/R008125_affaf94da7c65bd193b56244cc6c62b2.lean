import Mathlib

/- A ball is dropped straight down from a height of 16 feet. If it bounces back each time to a height one-half the height from which it last fell, how far will the ball have traveled when it hits the floor for the sixth time, in feet? -/
theorem algebra_19173 (h : ℕ → ℝ)
    (h₀ : h 0 = 16)
    (h₁ : ∀ n, h (n + 1) = h n / 2) :
    h 0 + 2 * ∑ i ∈ Finset.range 5, h (i + 1) = 47 := by
  simp only [Finset.sum_range, Fin.sum_univ_five]
  show h 0 + 2 * (h (0 + 1) + h (1 + 1) + h (2 + 1) + h (3 + 1) + h (4 + 1)) = 47
  simp only [h₀, zero_add, h₁, Nat.reduceAdd]
  ring
  