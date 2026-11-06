import Mathlib

theorem algebra_296908 {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (hsum : ∀ n, ∑ i in Finset.range n, a i = (3 * n + 1) / 2 - (n / 2) * a n) :
    a 0 = 1 ∧ a 1 = 2 ∧ a 2 = 3 ∧
    (∀ n, a n = n + 1) ∧
    (∀ n, ∑ i in Finset.range n, (1 / (a i - 1)) = n * (n + 1) * (n + 2) * (n + 3) / 8) := by 
  have h0 := hsum 0 
  simp at h0 
  all_goals linarith [ha 0, ha 1, ha 2]