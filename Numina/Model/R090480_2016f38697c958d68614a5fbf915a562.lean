import Mathlib

theorem algebra_248712 {a : ℕ → ℝ} (ha : a 0 ≠ a 1)
    (h : ∀ i, a (i - 1) + a (i + 1) = 2 * a i) :
    ∀ n, ∃ p : Polynomial ℝ, p.degree = 1 ∧
      p.coeff 0 = ∑ i in Finset.range (n + 1), a i * Nat.choose n i * (-1) ^ (n - i) ∧
      p.coeff 1 = ∑ i in Finset.range n, a (i + 1) * Nat.choose n (i + 1) * (-1) ^ (n - (i + 1)) := by
  intro n
  have h1 := h 0
  norm_num at h1 
  have h2 : a 1 = a 0 := by linarith
  have h3 : a 0 = a 1 := by linarith [h2]
  have h4 : a 0 = a 1 := by linarith [h2]
  exfalso
  exact ha (by linarith [h4])