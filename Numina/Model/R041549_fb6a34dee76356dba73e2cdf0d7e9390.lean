import Mathlib

theorem algebra_292146 {a : ℕ → ℝ} (ha : a 0 ≠ a 1)
    (h : ∀ i, a (i - 1) + a (i + 1) = 2 * a i) :
    ∀ n, ∃ p : ℝ → ℝ, (∀ x, p x = ∑ i ∈ Finset.range (n + 1),
      a i * Nat.choose n i * (1 - x) ^ (n - i)) ∧
    (∃ c d, ∀ x, p x = c * x + d) := by
  have h1 := h 0
  simp at h1
  have h2 : a 0 = a 1 := by
    linarith 
  have h4 : a 0 ≠ a 1 := ha
  contradiction